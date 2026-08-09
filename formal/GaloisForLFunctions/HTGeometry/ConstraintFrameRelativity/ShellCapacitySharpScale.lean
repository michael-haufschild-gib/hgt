import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellCapacityDepth

/-!
# The sharp depth scale of the Boolean shell capacity

The capacity of an ordered prime aperture is trapped between two constant multiples of the
second fugacity:

`c_F · p_1^{-σ} ≤ D(σ) ≤ C_F⁺ · p_1^{-σ}`,   `σ ≥ 0`,

with `c_F = π² (λ_1 - λ_0)² / (4 d λ_{d-1}²)` and `C_F⁺ = π² d (d-1) λ_{d-1}² / λ_0²`.  The
lower bound keeps only the clock gap of the two smallest primes in the Cauchy--Binet numerator
and bounds the energy moment by `d w_0 λ_{d-1}²`; the upper bound uses that every off-diagonal
weight product is at most `w_0 p_1^{-σ}`.

Consequently there is a uniform depth threshold `J_F(τ)` beyond which one power event strictly
contracts the capacity.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset

/-- Two distinct terms of a nonnegative finite sum. -/
theorem add_le_sum_of_ne {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) {a b : ι} (hab : a ≠ b) : f a + f b ≤ ∑ i, f i := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({a, b} : Finset ι)) (fun i _ _ => hf i)
  rwa [Finset.sum_pair hab] at h

namespace Aperture

variable (F : Aperture)

theorem second_le_of_lt {i j : Fin F.card} (h : i < j) : F.second ≤ j := by
  simp only [second, Fin.le_def]
  have := Fin.lt_def.mp h
  omega

theorem sq_clock_sub_le (i j : Fin F.card) :
    (F.clock i - F.clock j) ^ 2 ≤ (F.clock F.greatest) ^ 2 := by
  have hi := F.clock_pos i
  have hj := F.clock_pos j
  have hig := F.clock_le_greatest i
  have hjg := F.clock_le_greatest j
  nlinarith

/-! ## The Cauchy--Binet numerator -/

/-- The clock gap of the two smallest primes is a lower bound for the Gram determinant. -/
theorem gram_lower {σ : ℝ} :
    F.wt F.least σ * F.wt F.second σ * (F.clock F.second - F.clock F.least) ^ 2
      ≤ capA (fun i => F.wt i σ) * capC (fun i => F.wt i σ) F.clock
        - capB (fun i => F.wt i σ) F.clock ^ 2 := by
  classical
  rw [capA_mul_capC_sub_capB_sq]
  set w := fun i => F.wt i σ with hw
  have hnn : ∀ i : Fin F.card, (0 : ℝ) ≤ ∑ r, w i * w r * (F.clock i - F.clock r) ^ 2 := by
    intro i
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (mul_nonneg (F.wt_pos i σ).le (F.wt_pos r σ).le) (sq_nonneg _)
  have hpair := add_le_sum_of_ne (f := fun i => ∑ r, w i * w r * (F.clock i - F.clock r) ^ 2)
    hnn (F.least_lt_second).ne
  have h1 : w F.least * w F.second * (F.clock F.least - F.clock F.second) ^ 2
      ≤ ∑ r, w F.least * w r * (F.clock F.least - F.clock r) ^ 2 :=
    Finset.single_le_sum (f := fun r => w F.least * w r * (F.clock F.least - F.clock r) ^ 2)
      (fun r _ => mul_nonneg (mul_nonneg (F.wt_pos _ σ).le (F.wt_pos r σ).le) (sq_nonneg _))
      (Finset.mem_univ F.second)
  have h2 : w F.second * w F.least * (F.clock F.second - F.clock F.least) ^ 2
      ≤ ∑ r, w F.second * w r * (F.clock F.second - F.clock r) ^ 2 :=
    Finset.single_le_sum (f := fun r => w F.second * w r * (F.clock F.second - F.clock r) ^ 2)
      (fun r _ => mul_nonneg (mul_nonneg (F.wt_pos _ σ).le (F.wt_pos r σ).le) (sq_nonneg _))
      (Finset.mem_univ F.least)
  have hsq : (F.clock F.least - F.clock F.second) ^ 2
      = (F.clock F.second - F.clock F.least) ^ 2 := by ring
  rw [hsq] at h1
  have : 2 * (w F.least * w F.second * (F.clock F.second - F.clock F.least) ^ 2)
      ≤ ∑ p, ∑ r, w p * w r * (F.clock p - F.clock r) ^ 2 := by
    have hcomm : w F.second * w F.least = w F.least * w F.second := by ring
    rw [hcomm] at h2
    linarith
  linarith

/-- Every weight product with a clock gap is at most `w_0 p_1^{-σ} λ_{d-1}²`. -/
theorem term_le {i j : Fin F.card} {σ : ℝ} (hσ : 0 ≤ σ) :
    F.wt i σ * F.wt j σ * (F.clock i - F.clock j) ^ 2
      ≤ F.wt F.least σ * F.fug F.second σ * (F.clock F.greatest) ^ 2 := by
  have hbound : ∀ a b : Fin F.card, a < b →
      F.wt a σ * F.wt b σ ≤ F.wt F.least σ * F.fug F.second σ := by
    intro a b hab
    have hwa : F.wt a σ ≤ F.wt F.least σ := F.wt_le_wt_least a hσ
    have hwb : F.wt b σ ≤ F.fug F.second σ :=
      le_trans (F.wt_le_fug b σ) (F.fug_antitone (F.second_le_of_lt hab) hσ)
    exact mul_le_mul hwa hwb (F.wt_pos b σ).le (F.wt_pos F.least σ).le
  have hprod : F.wt i σ * F.wt j σ ≤ F.wt F.least σ * F.fug F.second σ ∨ i = j := by
    rcases lt_trichotomy i j with h | h | h
    · exact Or.inl (hbound i j h)
    · exact Or.inr h
    · refine Or.inl ?_
      have := hbound j i h
      linarith [this, (by ring : F.wt i σ * F.wt j σ = F.wt j σ * F.wt i σ)]
  rcases hprod with hprod | rfl
  · have hgap := F.sq_clock_sub_le i j
    have hnn : (0 : ℝ) ≤ F.wt i σ * F.wt j σ :=
      mul_nonneg (F.wt_pos i σ).le (F.wt_pos j σ).le
    have hgapnn : (0 : ℝ) ≤ (F.clock i - F.clock j) ^ 2 := sq_nonneg _
    have hrhsnn : (0 : ℝ) ≤ F.wt F.least σ * F.fug F.second σ :=
      mul_nonneg (F.wt_pos _ σ).le (F.fug_pos _ σ).le
    nlinarith
  · simp only [sub_self]
    have : (0 : ℝ) ≤ F.wt F.least σ * F.fug F.second σ * (F.clock F.greatest) ^ 2 :=
      mul_nonneg (mul_nonneg (F.wt_pos _ σ).le (F.fug_pos _ σ).le) (sq_nonneg _)
    simpa using this

theorem gram_upper {σ : ℝ} (hσ : 0 ≤ σ) :
    capA (fun i => F.wt i σ) * capC (fun i => F.wt i σ) F.clock
        - capB (fun i => F.wt i σ) F.clock ^ 2
      ≤ (F.card : ℝ) * ((F.card : ℝ) - 1)
        * (F.wt F.least σ * F.fug F.second σ * (F.clock F.greatest) ^ 2) := by
  classical
  rw [capA_mul_capC_sub_capB_sq]
  set M := F.wt F.least σ * F.fug F.second σ * (F.clock F.greatest) ^ 2 with hM
  have hMnn : (0 : ℝ) ≤ M :=
    mul_nonneg (mul_nonneg (F.wt_pos _ σ).le (F.fug_pos _ σ).le) (sq_nonneg _)
  have hinner : ∀ i : Fin F.card,
      ∑ r, F.wt i σ * F.wt r σ * (F.clock i - F.clock r) ^ 2 ≤ (F.card : ℝ) * M := by
    intro i
    have h : ∑ r, F.wt i σ * F.wt r σ * (F.clock i - F.clock r) ^ 2
        ≤ ∑ _r : Fin F.card, M :=
      Finset.sum_le_sum fun r _ => F.term_le hσ
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have houter : ∑ p, ∑ r, F.wt p σ * F.wt r σ * (F.clock p - F.clock r) ^ 2
      ≤ (F.card : ℝ) * ((F.card : ℝ) * M) := by
    have h : ∑ p, ∑ r, F.wt p σ * F.wt r σ * (F.clock p - F.clock r) ^ 2
        ≤ ∑ _p : Fin F.card, (F.card : ℝ) * M :=
      Finset.sum_le_sum fun p _ => hinner p
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have hd : (2 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast F.two_le_card
  have hd0 : (0 : ℝ) ≤ (F.card : ℝ) := by linarith
  have hd2 : (0 : ℝ) ≤ (F.card : ℝ) - 2 := by linarith
  nlinarith [houter, mul_nonneg (mul_nonneg hd2 hd0) hMnn]

/-! ## Bounds on the energy moment -/

theorem capC_le {σ : ℝ} (hσ : 0 ≤ σ) :
    capC (fun i => F.wt i σ) F.clock
      ≤ (F.card : ℝ) * (F.wt F.least σ * (F.clock F.greatest) ^ 2) := by
  have hterm : ∀ i : Fin F.card,
      F.wt i σ * F.clock i ^ 2 ≤ F.wt F.least σ * (F.clock F.greatest) ^ 2 := by
    intro i
    have h1 : F.wt i σ ≤ F.wt F.least σ := F.wt_le_wt_least i hσ
    have h2 : F.clock i ^ 2 ≤ (F.clock F.greatest) ^ 2 := by
      have hi := (F.clock_pos i).le
      have := F.clock_le_greatest i
      nlinarith
    exact mul_le_mul h1 h2 (sq_nonneg _) (F.wt_pos _ σ).le
  have h : capC (fun i => F.wt i σ) F.clock
      ≤ ∑ _i : Fin F.card, F.wt F.least σ * (F.clock F.greatest) ^ 2 :=
    Finset.sum_le_sum fun i _ => hterm i
  simpa [Finset.sum_const, nsmul_eq_mul] using h

theorem capC_ge {σ : ℝ} :
    F.wt F.least σ * (F.clock F.least) ^ 2 ≤ capC (fun i => F.wt i σ) F.clock :=
  Finset.single_le_sum (f := fun i => F.wt i σ * F.clock i ^ 2)
    (fun i _ => mul_nonneg (F.wt_pos i σ).le (sq_nonneg _)) (Finset.mem_univ F.least)

/-! ## The two-sided scale -/

/-- The lower scale constant `c_F`. -/
noncomputable def cLower : ℝ :=
  Real.pi ^ 2 * (F.clock F.second - F.clock F.least) ^ 2
    / (4 * (F.card : ℝ) * (F.clock F.greatest) ^ 2)

/-- The upper scale constant `C_F⁺`. -/
noncomputable def cUpper : ℝ :=
  Real.pi ^ 2 * (F.card : ℝ) * ((F.card : ℝ) - 1) * (F.clock F.greatest) ^ 2
    / (F.clock F.least) ^ 2

theorem cLower_pos : 0 < F.cLower := by
  have hgap : 0 < (F.clock F.second - F.clock F.least) ^ 2 := by
    have := F.clock_least_lt_second
    positivity
  have hd : (0 : ℝ) < F.card := by
    have := F.two_le_card
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) this
  have hL : 0 < (F.clock F.greatest) ^ 2 := by
    have := F.clock_pos F.greatest
    positivity
  rw [cLower]
  positivity

theorem cUpper_pos : 0 < F.cUpper := by
  have hd : (2 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast F.two_le_card
  have hd1 : (0 : ℝ) < (F.card : ℝ) - 1 := by linarith
  have hL : 0 < (F.clock F.greatest) ^ 2 := by
    have := F.clock_pos F.greatest
    positivity
  have hl : 0 < (F.clock F.least) ^ 2 := by
    have := F.clock_pos F.least
    positivity
  rw [cUpper]
  have hnum : 0 < Real.pi ^ 2 * (F.card : ℝ) * ((F.card : ℝ) - 1) * (F.clock F.greatest) ^ 2 := by
    have hpi : 0 < Real.pi ^ 2 := by positivity
    have : (0 : ℝ) < (F.card : ℝ) := by linarith
    positivity
  exact div_pos hnum hl

/-- **Sharp lower scale.**  `c_F p_1^{-σ} ≤ D(σ)`. -/
theorem cLower_mul_fug_le_capacity {σ : ℝ} (hσ : 0 ≤ σ) :
    F.cLower * F.fug F.second σ ≤ F.capacity σ := by
  have hCpos := F.energy_moment_pos σ
  have hCle := F.capC_le hσ
  have hnum := F.gram_lower (σ := σ)
  have hd : (0 : ℝ) < F.card := by
    have := F.two_le_card
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) this
  have hw0 := F.wt_pos F.least σ
  have hLg : 0 < (F.clock F.greatest) ^ 2 := by
    have := F.clock_pos F.greatest
    positivity
  have hChigh : (0 : ℝ) < (F.card : ℝ) * (F.wt F.least σ * (F.clock F.greatest) ^ 2) := by
    positivity
  have hnn : (0 : ℝ) ≤ F.wt F.least σ * F.wt F.second σ
      * (F.clock F.second - F.clock F.least) ^ 2 :=
    mul_nonneg (mul_nonneg hw0.le (F.wt_pos _ σ).le) (sq_nonneg _)
  have hratio :
      (F.wt F.least σ * F.wt F.second σ * (F.clock F.second - F.clock F.least) ^ 2)
          / ((F.card : ℝ) * (F.wt F.least σ * (F.clock F.greatest) ^ 2))
        ≤ (capA (fun i => F.wt i σ) * capC (fun i => F.wt i σ) F.clock
            - capB (fun i => F.wt i σ) F.clock ^ 2) / capC (fun i => F.wt i σ) F.clock := by
    refine div_le_div₀ (le_trans hnn hnum) hnum hCpos hCle
  simp only [capacity]
  rw [schurCapacity_eq_ratio hCpos]
  have hpi : (0 : ℝ) ≤ Real.pi ^ 2 := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hratio hpi)
  have hw2 : F.fug F.second σ / 4 ≤ F.wt F.second σ := F.fug_div_four_le_wt F.second hσ
  have hLHS : F.cLower * F.fug F.second σ
      = Real.pi ^ 2 * (((F.clock F.second - F.clock F.least) ^ 2 * F.fug F.second σ)
        / (4 * (F.card : ℝ) * (F.clock F.greatest) ^ 2)) := by
    rw [cLower]
    ring
  rw [hLHS]
  refine mul_le_mul_of_nonneg_left ?_ hpi
  have hden1 : (0 : ℝ) < 4 * (F.card : ℝ) * (F.clock F.greatest) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden1 hChigh]
  have hfac : (0 : ℝ) ≤ (F.clock F.second - F.clock F.least) ^ 2
      * ((F.card : ℝ) * (F.wt F.least σ * (F.clock F.greatest) ^ 2)) :=
    mul_nonneg (sq_nonneg _) hChigh.le
  have hdiff : F.fug F.second σ ≤ 4 * F.wt F.second σ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hdiff hfac]

/-- **Sharp upper scale.**  `D(σ) ≤ C_F⁺ p_1^{-σ}`. -/
theorem capacity_le_cUpper_mul_fug {σ : ℝ} (hσ : 0 ≤ σ) :
    F.capacity σ ≤ F.cUpper * F.fug F.second σ := by
  have hCpos := F.energy_moment_pos σ
  have hCge := F.capC_ge (σ := σ)
  have hnum := F.gram_upper hσ
  have hw0 := F.wt_pos F.least σ
  have hl : 0 < (F.clock F.least) ^ 2 := by
    have := F.clock_pos F.least
    positivity
  have hClow : (0 : ℝ) < F.wt F.least σ * (F.clock F.least) ^ 2 := by positivity
  have hNhigh : (0 : ℝ) ≤ (F.card : ℝ) * ((F.card : ℝ) - 1)
      * (F.wt F.least σ * F.fug F.second σ * (F.clock F.greatest) ^ 2) := by
    have hd : (2 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast F.two_le_card
    have h1 : (0 : ℝ) ≤ (F.card : ℝ) * ((F.card : ℝ) - 1) := by nlinarith
    have h2 : (0 : ℝ) ≤ F.wt F.least σ * F.fug F.second σ * (F.clock F.greatest) ^ 2 :=
      mul_nonneg (mul_nonneg hw0.le (F.fug_pos _ σ).le) (sq_nonneg _)
    exact mul_nonneg h1 h2
  have hratio :
      (capA (fun i => F.wt i σ) * capC (fun i => F.wt i σ) F.clock
          - capB (fun i => F.wt i σ) F.clock ^ 2) / capC (fun i => F.wt i σ) F.clock
        ≤ ((F.card : ℝ) * ((F.card : ℝ) - 1)
            * (F.wt F.least σ * F.fug F.second σ * (F.clock F.greatest) ^ 2))
          / (F.wt F.least σ * (F.clock F.least) ^ 2) :=
    div_le_div₀ hNhigh hnum hClow hCge
  simp only [capacity]
  rw [schurCapacity_eq_ratio hCpos]
  have hpi : (0 : ℝ) ≤ Real.pi ^ 2 := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hratio hpi) ?_
  have hRHS : F.cUpper * F.fug F.second σ
      = Real.pi ^ 2 * (((F.card : ℝ) * ((F.card : ℝ) - 1) * (F.clock F.greatest) ^ 2
        * F.fug F.second σ) / (F.clock F.least) ^ 2) := by
    rw [cUpper]
    ring
  rw [hRHS]
  refine mul_le_mul_of_nonneg_left ?_ hpi
  rw [div_le_div_iff₀ hClow hl]
  apply le_of_eq
  ring

/-! ## The uniform jump threshold -/

/-- The uniform depth-jump threshold `J_F(τ)`. -/
noncomputable def jumpThreshold (τ : ℝ) : ℕ :=
  1 + ⌊Real.log (F.cUpper / F.cLower) / (τ * F.clock F.second)⌋₊

/-- The second fugacity at two depths differs by an exact exponential factor. -/
theorem fug_second_depth (m n : ℕ) (τ : ℝ) :
    F.fug F.second ((m : ℝ) * τ)
      = F.fug F.second ((n : ℝ) * τ) * Real.exp (((n : ℝ) - m) * (τ * F.clock F.second)) := by
  rw [fug, fug, Real.rpow_def_of_pos (F.prime_pos _), Real.rpow_def_of_pos (F.prime_pos _),
    ← Real.exp_add]
  congr 1
  simp only [clock]
  ring

/-- **Uniform jump threshold.**  Once the depth gap reaches `J_F(τ)` the capacity strictly
contracts. -/
theorem capacity_lt_of_jumpThreshold_le {τ : ℝ} (hτ : 0 < τ) {m n : ℕ}
    (h : m + F.jumpThreshold τ ≤ n) :
    F.capacity ((n : ℝ) * τ) < F.capacity ((m : ℝ) * τ) := by
  have hclk := F.clock_pos F.second
  have htaulog : 0 < τ * F.clock F.second := mul_pos hτ hclk
  have hJ : Real.log (F.cUpper / F.cLower) / (τ * F.clock F.second)
      < (F.jumpThreshold τ : ℝ) := by
    have hfl := Nat.lt_floor_add_one
      (Real.log (F.cUpper / F.cLower) / (τ * F.clock F.second))
    rw [jumpThreshold]
    push_cast
    linarith
  have hnm : (F.jumpThreshold τ : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
    have : ((m + F.jumpThreshold τ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  have hLlt : Real.log (F.cUpper / F.cLower)
      < ((n : ℝ) - (m : ℝ)) * (τ * F.clock F.second) := by
    rw [div_lt_iff₀ htaulog] at hJ
    nlinarith [hJ, hnm, htaulog]
  have hexp : F.cUpper / F.cLower
      < Real.exp (((n : ℝ) - (m : ℝ)) * (τ * F.clock F.second)) := by
    have hlt := Real.exp_lt_exp.mpr hLlt
    rwa [Real.exp_log (div_pos F.cUpper_pos F.cLower_pos)] at hlt
  have hprod : F.cUpper
      < F.cLower * Real.exp (((n : ℝ) - (m : ℝ)) * (τ * F.clock F.second)) := by
    rw [div_lt_iff₀ F.cLower_pos] at hexp
    linarith
  have hx := F.fug_pos F.second ((n : ℝ) * τ)
  have hkey : F.cUpper * F.fug F.second ((n : ℝ) * τ)
      < F.cLower * F.fug F.second ((m : ℝ) * τ) := by
    rw [F.fug_second_depth m n τ]
    nlinarith [hx, hprod]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) * τ := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) * τ := by positivity
  have h1 := F.capacity_le_cUpper_mul_fug hn0
  have h2 := F.cLower_mul_fug_le_capacity hm0
  linarith

end Aperture

end HTGeometry.ConstraintFrameRelativity
