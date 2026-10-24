import GaloisForLFunctions.RHTower.FactorialCriticalWindowAffineComparison
import GaloisForLFunctions.RHTower.FactorialCriticalWindowAffineHead
import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalPrimeChannelCrossBlockDecay
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelNegativeDefinite
import GaloisForLFunctions.HTGeometry.SzegoTail

/-!
# The linear window of the critical prime channel

The limiting critical prime form is negative definite, `P∞(b) ≤ −(4/(7000π⁴)) Σ b²`, and the actual
prime matrix on a *fixed* support is eventually negative definite. Here the support grows: on every
**linear window** of scales `N ≤ m + 1 ≤ (1 + δ)N`, a family whose dimension grows linearly in `N`,
the actual critical prime channel stays negative definite,

  `criticalPrimeEnergy T b ≤ −(2/(7000π⁴)) Σ b²`   for `N ≥ N₀`

(`exists_linearWindow_criticalPrimeEnergy_le`).

**Mechanism.** `P(b) = Σ_r Λ(r)/r ∫₁^∞ v⁻² B(v) B(rv) dv` (`criticalPrimeAtom_eq`), and each
dilation correlation is the harmonic double series `(4/π⁴) Σ_{k,l} w_k w_l ∫ v⁻² h_k(v) h_l(rv)`,
while its limit keeps exactly the resonances `k = lr` with the pattern masses `J_k`
(`hasSum_correlationLimit_prod`). Large dilations are paid by the window decay `√(2/r)` on both
sides, high harmonics by the support-independent bound on every harmonic pair. In the finite head
`k, l ≤ K`, `r ≤ R` the actual clock is compared with the affine clock and the affine head with the
resonant masses, both with errors uniform in the dimension. Choosing the prime cutoff, the harmonic
cutoff, the window width and the threshold in this order gives `|P − P∞| ≤ (2/(7000π⁴)) Σ b²`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ### Harmonic series of the actual and the limiting dilation correlations -/

/-- **Harmonic series of a critical dilation correlation**:
`∫₁^∞ v⁻² B(v) B(rv) = Σ_{k,l} (4/π⁴) w_k w_l ∫₁^∞ v⁻² h_k(v) h_l(rv)`. -/
theorem hasSum_integral_criticalWindowWeight_dilate (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) :
    HasSum (fun p : ℕ × ℕ => 4 / Real.pi ^ 4 *
        (dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2) *
          ∫ v in Ioi 1, criticalWindowWeight v *
            (realHarmonicLayer S b p.1 v * realHarmonicLayer S b p.2 (r * v)))
      (∫ v in Ioi 1, criticalWindowWeight v *
        (realPhaseCombination S b v * realPhaseCombination S b (r * v))) :=
  (hasSum_integral_weight_realPhaseCombination_dilate integrableOn_criticalWindowWeight S S b b
    r).congr_fun fun p => by
      rw [integral_mul_realHarmonicLayer_mul_dilate_bilinear integrableOn_criticalWindowWeight]

/-- The limiting correlation is a double series over the resonances `k = l r`. -/
theorem hasSum_correlationLimit_prod (T : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) :
    HasSum (fun p : ℕ × ℕ => 4 / Real.pi ^ 4 *
        (dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2) *
          (if p.1 = p.2 * r then factorialCriticalPatternHarmonicMass T b p.1 else 0))
      (factorialCriticalTranslatedCorrelationLimit T b r) := by
  set f : ℕ × ℕ → ℝ := fun p => 4 / Real.pi ^ 4 *
    (dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2) *
      (if p.1 = p.2 * r then factorialCriticalPatternHarmonicMass T b p.1 else 0)
  set e : ℕ → ℕ × ℕ := fun l => (l * r, l)
  have he : Function.Injective e := fun x y h => (Prod.ext_iff.mp h).2
  have hzero : ∀ p ∉ Set.range e, f p = 0 := by
    intro p hp
    have hne : p.1 ≠ p.2 * r := fun h => hp ⟨p.2, Prod.ext h.symm rfl⟩
    simp only [f, if_neg hne, mul_zero]
  rw [← he.hasSum_iff hzero]
  have hcomp : f ∘ e = fun l => 4 / Real.pi ^ 4 * (dyadicHarmonicWeight (r * l) *
      dyadicHarmonicWeight l * factorialCriticalPatternHarmonicMass T b (r * l)) := by
    funext l
    simp only [Function.comp, f, e, if_true, mul_comm l r]
    ring
  rw [hcomp]
  unfold factorialCriticalTranslatedCorrelationLimit
  refine HasSum.mul_left _ (Summable.hasSum ?_)
  set E := ∑ j ∈ T, b j ^ 2
  refine Summable.of_norm_bounded (summable_abs_dyadicHarmonicWeight.mul_right (4 * E)) fun l => ?_
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  have hm : 0 < r * l ∨ r = 0 := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.mul_pos h hl)
  rcases hm with hm | hr0
  · rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (factorialCriticalPatternHarmonicMass_nonneg T b (r * l))]
    have h1 : |dyadicHarmonicWeight (r * l)| ≤ 1 := (abs_dyadicHarmonicWeight_le _).trans (by
      rw [div_le_one (by positivity)]; exact_mod_cast Nat.one_le_pow _ _ hm)
    have h2 := factorialCriticalPatternHarmonicMass_le T b hm
    have h0 := factorialCriticalPatternHarmonicMass_nonneg T b (r * l)
    calc |dyadicHarmonicWeight (r * l)| * |dyadicHarmonicWeight l| *
          factorialCriticalPatternHarmonicMass T b (r * l)
        ≤ 1 * |dyadicHarmonicWeight l| * (4 * E) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2 h0 (by positivity)
      _ = |dyadicHarmonicWeight l| * (4 * E) := by ring
  · subst hr0
    simp only [zero_mul, dyadicHarmonicWeight_zero, norm_zero]
    positivity

/-- The limiting correlation decays like `r⁻²`. -/
theorem abs_correlationLimit_le (T : Finset ℕ) (b : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r) :
    |factorialCriticalTranslatedCorrelationLimit T b r| ≤
      4 / Real.pi ^ 4 * (7 / 4 * (4 * ∑ j ∈ T, b j ^ 2)) / (r : ℝ) ^ 2 := by
  set E := ∑ j ∈ T, b j ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold factorialCriticalTranslatedCorrelationLimit
  have hb : ∀ l : ℕ, ‖dyadicHarmonicWeight (r * l) * dyadicHarmonicWeight l *
      factorialCriticalPatternHarmonicMass T b (r * l)‖ ≤
        |dyadicHarmonicWeight l| * (4 * E) / (r : ℝ) ^ 2 := by
    intro l
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp only [dyadicHarmonicWeight_zero, mul_zero, zero_mul, norm_zero, abs_zero]; positivity
    have hm : 0 < r * l := Nat.mul_pos (by omega) hl
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (factorialCriticalPatternHarmonicMass_nonneg T b (r * l))]
    have h1 : |dyadicHarmonicWeight (r * l)| ≤ 1 / (r : ℝ) ^ 2 := by
      refine (abs_dyadicHarmonicWeight_le _).trans ?_
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
      calc (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 * (l : ℝ) ^ 2 :=
            le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hl1)
        _ = ((r : ℝ) * l) ^ 2 := by ring
    have h2 := factorialCriticalPatternHarmonicMass_le T b hm
    have h0 := factorialCriticalPatternHarmonicMass_nonneg T b (r * l)
    calc |dyadicHarmonicWeight (r * l)| * |dyadicHarmonicWeight l| *
          factorialCriticalPatternHarmonicMass T b (r * l)
        ≤ 1 / (r : ℝ) ^ 2 * |dyadicHarmonicWeight l| * (4 * E) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2 h0 (by positivity)
      _ = |dyadicHarmonicWeight l| * (4 * E) / (r : ℝ) ^ 2 := by ring
  have hs : Summable fun l : ℕ => |dyadicHarmonicWeight l| * (4 * E) / (r : ℝ) ^ 2 :=
    (summable_abs_dyadicHarmonicWeight.mul_right (4 * E)).div_const _
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi ^ 4), mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs)).trans
    ((Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs) hs).trans ?_)
  rw [tsum_div_const, tsum_mul_right]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right tsum_abs_dyadicHarmonicWeight_le
    (by positivity)) (by positivity)

/-! ### Tails and the box–tail estimate -/

/-- The tail `Σ_{k > K} f k` of a series. -/
def seriesTailMass (f : ℕ → ℝ) (K : ℕ) : ℝ := ∑' k : ℕ, if k < K + 1 then 0 else f k

theorem summable_seriesTail {f : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hf : Summable f) (K : ℕ) :
    Summable fun k : ℕ => if k < K + 1 then 0 else f k :=
  Summable.of_nonneg_of_le (fun k => by split_ifs <;> simp [hf0])
    (fun k => by split_ifs <;> simp [hf0]) hf

theorem seriesTailMass_nonneg {f : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (K : ℕ) :
    0 ≤ seriesTailMass f K :=
  tsum_nonneg fun k => by split_ifs <;> simp [hf0]

theorem tendsto_seriesTailMass {f : ℕ → ℝ} (hf : Summable f) :
    Tendsto (seriesTailMass f) atTop (𝓝 0) :=
  (HTGeometry.tendsto_tsum_tail_ite hf).comp (tendsto_add_atTop_nat 1)

/-- **Box–tail estimate for a doubly weighted series.** If `|F(k,l)| ≤ A |w_k||w_l|` on the box
`k, l ≤ K` and `|F(k,l)| ≤ C |w_k||w_l|` everywhere, then `|Σ F| ≤ A W² + 2 C W τ_K`, where
`W = Σ |w_k|` and `τ_K = Σ_{k > K} |w_k|`. -/
theorem abs_hasSum_le_box_tail {F : ℕ × ℕ → ℝ} {s : ℝ} (hF : HasSum F s) (K : ℕ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbox : ∀ p : ℕ × ℕ, p.1 ≤ K → p.2 ≤ K →
      |F p| ≤ A * (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|))
    (hall : ∀ p : ℕ × ℕ, |F p| ≤ C * (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|)) :
    |s| ≤ A * (∑' k, |dyadicHarmonicWeight k|) ^ 2 +
      2 * C * (∑' k, |dyadicHarmonicWeight k|) *
        seriesTailMass (fun k => |dyadicHarmonicWeight k|) K := by
  set a : ℕ → ℝ := fun k => |dyadicHarmonicWeight k| with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => abs_nonneg _
  have hs : Summable a := summable_abs_dyadicHarmonicWeight
  set t : ℕ → ℝ := fun k => if k < K + 1 then 0 else a k with ht
  have ht0 : ∀ k, 0 ≤ t k := fun k => by simp only [t]; split_ifs <;> simp [ha0]
  have hts : Summable t := summable_seriesTail ha0 hs K
  have hW := hs.hasSum
  have hT : HasSum t (seriesTailMass a K) := hts.hasSum
  have h1 := hW.mul hW (hs.mul_of_nonneg hs ha0 ha0)
  have h2 := hT.mul hW (hts.mul_of_nonneg hs ht0 ha0)
  have h3 := hW.mul hT (hs.mul_of_nonneg hts ha0 ht0)
  have hm := (h1.mul_left A).add ((h2.add h3).mul_left C)
  have hb := hF.norm_le_of_bounded hm fun p => by
    rw [Real.norm_eq_abs]
    have hA' : 0 ≤ A * (a p.1 * a p.2) := mul_nonneg hA (mul_nonneg (ha0 _) (ha0 _))
    have hC' : 0 ≤ C * (t p.1 * a p.2 + a p.1 * t p.2) :=
      mul_nonneg hC (add_nonneg (mul_nonneg (ht0 _) (ha0 _)) (mul_nonneg (ha0 _) (ht0 _)))
    by_cases hp : p.1 ≤ K ∧ p.2 ≤ K
    · have := hbox p hp.1 hp.2
      linarith
    · have hle : a p.1 * a p.2 ≤ t p.1 * a p.2 + a p.1 * t p.2 := by
        rcases not_and_or.mp hp with h | h
        · have e : t p.1 = a p.1 := if_neg (by omega)
          rw [e]; linarith [mul_nonneg (ha0 p.1) (ht0 p.2)]
        · have e : t p.2 = a p.2 := if_neg (by omega)
          rw [e]; linarith [mul_nonneg (ht0 p.1) (ha0 p.2)]
      have := hall p
      linarith [mul_le_mul_of_nonneg_left hle hC]
  rw [Real.norm_eq_abs] at hb
  refine hb.trans (le_of_eq ?_)
  ring

/-! ### The dilation correlation against its limit -/

/-- The head error on a linear window: affine-clock comparison of the box `k ≤ K`, `lr ≤ M`
plus the off-resonant affine entries. -/
def linearWindowHeadError (K M : ℕ) (N δ : ℝ) : ℝ :=
  criticalWindowAffineCorrelationError K M N + 6 * criticalWindowCosineDecay * (δ + 1 / N)

theorem criticalWindowAffineCorrelationError_mono {k l K M : ℕ} (hk : k ≤ K) (hl : l ≤ M)
    {N : ℝ} (hN : 0 < N) :
    criticalWindowAffineCorrelationError k l N ≤ criticalWindowAffineCorrelationError K M N := by
  have hU := criticalWindowHarmonicBound_nonneg
  have hk' : Real.pi ^ 2 * k / (140 * N) ≤ Real.pi ^ 2 * K / (140 * N) := by
    gcongr
  have hl' : Real.pi ^ 2 * l / (140 * N) ≤ Real.pi ^ 2 * M / (140 * N) := by
    gcongr
  have hk0 : 0 ≤ Real.pi ^ 2 * k / (140 * N) := by positivity
  have hl0 : 0 ≤ Real.pi ^ 2 * l / (140 * N) := by positivity
  unfold criticalWindowAffineCorrelationError
  gcongr

/-- **The dilation correlation against its resonant limit.** On a window
`N ≤ n + 1 ≤ (1 + δ)N`, for `r ≥ 1` and a harmonic cutoff `K` with `Kr ≤ M`, `(K + M)δ ≤ 1/4` and
`K + M ≤ N`, `|∫ v⁻² B(v)B(rv) − C∞(r)| ≤ (4/π⁴)(H W² + 2(U + 4) W τ_K) Σ b²`, where `H` is the
head error, `W = Σ|w_k|` and `τ_K = Σ_{k>K}|w_k|`. -/
theorem abs_integral_criticalWindowWeight_dilate_sub_limit_le (S : Finset ℕ) (b : ℕ → ℝ)
    {N δ : ℝ} (hN : 2 ≤ N) (hδ : 0 ≤ δ)
    (hS : ∀ n ∈ S, N ≤ ((n + 1 : ℕ) : ℝ) ∧ ((n + 1 : ℕ) : ℝ) ≤ (1 + δ) * N)
    {r K M : ℕ} (hr : 1 ≤ r) (hKM : K * r ≤ M) (hsmall : ((K : ℝ) + M) * δ ≤ 1 / 4)
    (hlarge : (K : ℝ) + M ≤ N) :
    |(∫ v in Ioi 1, criticalWindowWeight v *
        (realPhaseCombination S b v * realPhaseCombination S b (r * v))) -
      factorialCriticalTranslatedCorrelationLimit S b r| ≤
      4 / Real.pi ^ 4 * (linearWindowHeadError K M N δ * (∑' k, |dyadicHarmonicWeight k|) ^ 2 +
        2 * (criticalWindowHarmonicBound + 4) * (∑' k, |dyadicHarmonicWeight k|) *
          seriesTailMass (fun k => |dyadicHarmonicWeight k|) K) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU := criticalWindowHarmonicBound_nonneg
  have hD := criticalWindowCosineDecay_nonneg
  have hc4 : 0 < 4 / Real.pi ^ 4 := by positivity
  have hN0 : 0 < N := by linarith
  have hH : 0 ≤ linearWindowHeadError K M N δ := by
    unfold linearWindowHeadError criticalWindowAffineCorrelationError; positivity
  have hF := (hasSum_integral_criticalWindowWeight_dilate S b r).sub
    (hasSum_correlationLimit_prod S b r)
  have key := abs_hasSum_le_box_tail hF K (A := 4 / Real.pi ^ 4 * (linearWindowHeadError K M N δ * E))
    (C := 4 / Real.pi ^ 4 * ((criticalWindowHarmonicBound + 4) * E)) (by positivity) (by positivity)
    ?_ ?_
  · refine key.trans (le_of_eq ?_)
    ring
  · rintro ⟨k, l⟩ hk hl
    dsimp only at hk hl ⊢
    rw [← mul_sub, abs_mul, abs_mul, abs_of_pos hc4, abs_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp
    rcases Nat.eq_zero_or_pos l with rfl | hl1
    · simp
    have hq1 : 1 ≤ l * r := Nat.mul_pos hl1 hr
    have hlr : l * r ≤ M := (Nat.mul_le_mul_right r hl).trans hKM
    have hkq : (k : ℝ) + ((l * r : ℕ) : ℝ) ≤ K + M := by
      have : k + l * r ≤ K + M := by omega
      exact_mod_cast this
    have hI : ∫ v in Ioi 1, criticalWindowWeight v *
          (realHarmonicLayer S b k v * realHarmonicLayer S b l (r * v)) =
        ∫ v, realHarmonicLayer S b k v * realHarmonicLayer S b (l * r) v ∂criticalWindowMeasure := by
      rw [integral_criticalWindowMeasure_eq_weight]
      simp_rw [realHarmonicLayer_dilate_nat]
    have h1 := abs_integral_criticalWindow_harmonics_sub_affine_le b hk1 hq1 hN0
      (fun n hn => (hS n hn).1)
    have h2 := abs_integral_criticalWindow_affine_sub_mass_le b hk1 hq1 hN hδ
      ((mul_le_mul_of_nonneg_right hkq hδ).trans hsmall) (hkq.trans hlarge) hS
    have h3 := criticalWindowAffineCorrelationError_mono hk hlr hN0
    have key2 : |(∫ v in Ioi 1, criticalWindowWeight v *
          (realHarmonicLayer S b k v * realHarmonicLayer S b l (r * v))) -
        (if k = l * r then factorialCriticalPatternHarmonicMass S b k else 0)| ≤
        linearWindowHeadError K M N δ * E := by
      rw [hI]
      refine (abs_sub_le _ (∫ v, realAffineHarmonicLayer S b k v *
        realAffineHarmonicLayer S b (l * r) v ∂criticalWindowMeasure) _).trans ?_
      refine (add_le_add (h1.trans (mul_le_mul_of_nonneg_right h3 hE)) h2).trans (le_of_eq ?_)
      unfold linearWindowHeadError
      ring
    calc 4 / Real.pi ^ 4 * (|dyadicHarmonicWeight k| * |dyadicHarmonicWeight l|) * |_| ≤
        4 / Real.pi ^ 4 * (|dyadicHarmonicWeight k| * |dyadicHarmonicWeight l|) *
          (linearWindowHeadError K M N δ * E) := mul_le_mul_of_nonneg_left key2 (by positivity)
      _ = _ := by ring
  · rintro ⟨k, l⟩
    dsimp only
    rw [← mul_sub, abs_mul, abs_mul, abs_of_pos hc4, abs_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp
    rcases Nat.eq_zero_or_pos l with rfl | hl1
    · simp
    have hI := abs_integral_criticalWindowWeight_harmonics_le S b hk1 hl1 hr
    have hJ : |(if k = l * r then factorialCriticalPatternHarmonicMass S b k else 0)| ≤ 4 * E := by
      split_ifs
      · rw [abs_of_nonneg (factorialCriticalPatternHarmonicMass_nonneg S b k)]
        exact factorialCriticalPatternHarmonicMass_le S b hk1
      · simp only [abs_zero]; positivity
    have key2 := (abs_sub _ _).trans (add_le_add hI hJ)
    calc 4 / Real.pi ^ 4 * (|dyadicHarmonicWeight k| * |dyadicHarmonicWeight l|) * |_| ≤
        4 / Real.pi ^ 4 * (|dyadicHarmonicWeight k| * |dyadicHarmonicWeight l|) *
          (criticalWindowHarmonicBound * E + 4 * E) := mul_le_mul_of_nonneg_left key2 (by positivity)
      _ = _ := by ring

/-! ### The prime sum -/

/-- The critical dilation correlation splits along the collar. -/
theorem integral_criticalWindowWeight_dilate_eq (T : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) :
    ∫ v in Ioi 1, criticalWindowWeight v *
        (realPhaseCombination T b v * realPhaseCombination T b (r * v)) =
      (∫ v in Ioi 1, criticalCollarWeight v *
          (realPhaseCombination T b v * realPhaseCombination T b (r * v))) +
        ∫ v in Ioi 1, criticalEndpointWeight v *
          (realPhaseCombination T b v * realPhaseCombination T b (r * v)) := by
  set R := realPhaseCombination T b
  have hRc : Continuous fun v => R v * R (r * v) := by
    have : Continuous R := by
      have h := continuous_factorialPhaseCombination T (fun n => (b n : ℂ))
      exact (Complex.continuous_re.comp h).congr fun v => factorialPhaseCombination_re_eq T b v
    exact this.mul (this.comp (continuous_const.mul continuous_id))
  have hRb : ∀ v, ‖R v * R (r * v)‖ ≤ (2 * ∑ n ∈ T, |b n|) * (2 * ∑ n ∈ T, |b n|) := fun v => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_realPhaseCombination_le_two_mul T b v)
      (abs_realPhaseCombination_le_two_mul T b _) (abs_nonneg _) (by positivity)
  have h1 : IntegrableOn (fun v => criticalCollarWeight v * (R v * R (r * v))) (Ioi 1) :=
    integrableOn_criticalCollarWeight.mul_bdd hRc.aestronglyMeasurable (Eventually.of_forall hRb)
  have h2 : IntegrableOn (fun v => criticalEndpointWeight v * (R v * R (r * v))) (Ioi 1) :=
    integrableOn_criticalEndpointWeight.mul_bdd hRc.aestronglyMeasurable (Eventually.of_forall hRb)
  rw [← integral_add h1 h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  rw [← add_mul, criticalCollarWeight_add_criticalEndpointWeight (lt_trans one_pos hv)]
  rfl

/-- **The actual prime atom in clock form**: `atom_r = Λ(r)/r ∫₁^∞ v⁻² B(v) B(rv)`. -/
theorem criticalPrimeAtom_eq (T : Finset ℕ) (b : ℕ → ℝ) {r : ℕ} (hr : 2 ≤ r) :
    criticalPrimeAtom T b r = (ArithmeticFunction.vonMangoldt r : ℝ) / r *
      ∫ v in Ioi 1, criticalWindowWeight v *
        (realPhaseCombination T b v * realPhaseCombination T b (r * v)) := by
  unfold criticalPrimeAtom
  rw [if_pos hr, integral_criticalFactorialSource_mul_dilate_eq T b (by omega),
    ← integral_criticalWindowWeight_dilate_eq]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hs : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  rw [show (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r *
      ∫ v in Ioi 1, criticalWindowWeight v *
        (realPhaseCombination T b v * realPhaseCombination T b (r * v))) =
      (ArithmeticFunction.vonMangoldt r : ℝ) * (∫ v in Ioi 1, criticalWindowWeight v *
        (realPhaseCombination T b v * realPhaseCombination T b (r * v))) /
          (Real.sqrt r * Real.sqrt r) by field_simp, hs]
  ring

/-- **Large dilations on a window.** On scales in `[N, 2N]`,
`|∫₁^∞ v⁻² B(v) B(rv)| ≤ (4/π⁴) K_W √(2/r) Σ b²`. -/
theorem abs_integral_criticalWindowWeight_dilate_le_of_window {T : Finset ℕ} {N : ℕ} (hN : 1 ≤ N)
    (hT : ScaleWindow T N 2) (b : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r) :
    |∫ v in Ioi 1, criticalWindowWeight v *
        (realPhaseCombination T b v * realPhaseCombination T b (r * v))| ≤
      4 / Real.pi ^ 4 * (criticalWindowConstant * Real.sqrt (2 / r)) * ∑ n ∈ T, b n ^ 2 := by
  rw [integral_criticalWindowWeight_dilate_eq]
  refine (abs_criticalWindowCorrelation_le hN (by norm_num) hT b hr).trans ?_
  have hK := criticalWindowConstant_nonneg
  have hE : 0 ≤ ∑ n ∈ T, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  push_cast
  gcongr
  exact min_le_right _ _

theorem envelopePrimeMajorant_one_eq {r : ℕ} (hr : 2 ≤ r) :
    envelopePrimeMajorant 1 r =
      (ArithmeticFunction.vonMangoldt r : ℝ) / ((r : ℝ) * Real.sqrt r) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  unfold envelopePrimeMajorant
  rw [if_pos hr, Real.rpow_add hr0, Real.rpow_one, Real.sqrt_eq_rpow]

/-- **The actual prime channel against its limit on a linear window.** For scales
`N ≤ n + 1 ≤ (1 + δ)N` with `δ ≤ 1`, a prime cutoff `R` and a harmonic cutoff `K` with
`(K + KR)δ ≤ 1/4` and `K + KR ≤ N`,
`|P − P∞| ≤ ((R + 1)(4/π⁴)(H W² + 2(U + 4)W τ_K) + (4/π⁴)(K_W √2 + 7) σ_R) Σ b²`,
with `σ_R = Σ_{r > R} Λ(r) r^{-3/2}`. -/
theorem abs_criticalPrimeEnergy_sub_limit_le (T : Finset ℕ) (b : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hT : ∀ n ∈ T, (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ∧ ((n + 1 : ℕ) : ℝ) ≤ (1 + δ) * N) {R K : ℕ}
    (hsmall : ((K : ℝ) + ((K * R : ℕ) : ℝ)) * δ ≤ 1 / 4)
    (hlarge : (K : ℝ) + ((K * R : ℕ) : ℝ) ≤ N) :
    |criticalPrimeEnergy T b - factorialCriticalTranslatedPrimeLimit T b| ≤
      ((R + 1) * (4 / Real.pi ^ 4 *
          (linearWindowHeadError K (K * R) N δ * (∑' k, |dyadicHarmonicWeight k|) ^ 2 +
            2 * (criticalWindowHarmonicBound + 4) * (∑' k, |dyadicHarmonicWeight k|) *
              seriesTailMass (fun k => |dyadicHarmonicWeight k|) K)) +
        4 / Real.pi ^ 4 * (criticalWindowConstant * Real.sqrt 2 + 7) *
          seriesTailMass (envelopePrimeMajorant 1) R) * ∑ n ∈ T, b n ^ 2 := by
  set E := ∑ n ∈ T, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU := criticalWindowHarmonicBound_nonneg
  have hD := criticalWindowCosineDecay_nonneg
  have hKW := criticalWindowConstant_nonneg
  have hc4 : 0 < 4 / Real.pi ^ 4 := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set W := ∑' k, |dyadicHarmonicWeight k|
  have hW : 0 ≤ W := tsum_nonneg fun _ => abs_nonneg _
  set τ := seriesTailMass (fun k => |dyadicHarmonicWeight k|) K
  have hτ : 0 ≤ τ := seriesTailMass_nonneg (fun _ => abs_nonneg _) K
  have hH : 0 ≤ linearWindowHeadError K (K * R) N δ := by
    unfold linearWindowHeadError criticalWindowAffineCorrelationError; positivity
  set Hd := 4 / Real.pi ^ 4 * (linearWindowHeadError K (K * R) N δ * W ^ 2 +
    2 * (criticalWindowHarmonicBound + 4) * W * τ) * E
  have hHd : 0 ≤ Hd := by positivity
  set Ct := 4 / Real.pi ^ 4 * (criticalWindowConstant * Real.sqrt 2 + 7)
  have hCt : 0 ≤ Ct := by positivity
  have hW2 : ScaleWindow T N 2 := fun n hn => by
    obtain ⟨h1, h2⟩ := hT n hn
    have h3 : ((n + 1 : ℕ) : ℝ) ≤ 2 * N := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ1) hN0.le]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h3⟩
  have hA : Summable (criticalPrimeAtom T b) :=
    summable_abs_iff.mp (summable_criticalFactorialSource_prime T b)
  have hC : Summable fun r : ℕ => if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
      factorialCriticalTranslatedCorrelationLimit T b r else 0 :=
    summable_abs_iff.mp (summable_factorialCriticalTranslatedPrimeLimit_atoms T b)
  have hdiff : HasSum (fun r => criticalPrimeAtom T b r -
      if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
        factorialCriticalTranslatedCorrelationLimit T b r else 0)
      (criticalPrimeEnergy T b - factorialCriticalTranslatedPrimeLimit T b) :=
    hA.hasSum.sub hC.hasSum
  have hM1 : Summable (envelopePrimeMajorant 1) :=
    summable_envelopePrimeMajorant_of_half_lt (by norm_num)
  have hhead : HasSum (fun r : ℕ => if r ≤ R then Hd else 0) ((R + 1) * Hd) := by
    have h : HasSum (fun r : ℕ => if r ≤ R then Hd else 0)
        (∑ r ∈ Finset.range (R + 1), if r ≤ R then Hd else 0) :=
      hasSum_sum_of_ne_finset_zero fun r hr => if_neg (by simp at hr; omega)
    convert h using 1
    rw [Finset.sum_congr rfl fun r hr => if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  have htail : HasSum (fun r => Ct * E * (if r < R + 1 then 0 else envelopePrimeMajorant 1 r))
      (Ct * E * seriesTailMass (envelopePrimeMajorant 1) R) :=
    (summable_seriesTail (envelopePrimeMajorant_nonneg 1) hM1 R).hasSum.mul_left (Ct * E)
  have hb := hdiff.norm_le_of_bounded (hhead.add htail) fun r => by
    rw [Real.norm_eq_abs]
    have hm0 : 0 ≤ Ct * E * (if r < R + 1 then 0 else envelopePrimeMajorant 1 r) :=
      mul_nonneg (mul_nonneg hCt hE) (by split_ifs <;> simp [envelopePrimeMajorant_nonneg])
    have hh0 : 0 ≤ (if r ≤ R then Hd else 0) := by split_ifs <;> simp [hHd]
    by_cases hr2 : 2 ≤ r
    swap
    · have h0 : criticalPrimeAtom T b r = 0 := by
        unfold criticalPrimeAtom; rw [if_neg hr2, zero_mul]
      rw [h0, if_neg hr2, sub_zero, abs_zero]
      exact add_nonneg hh0 hm0
    have hΛ0 := vonMangoldt_div_nonneg r
    have hΛ1 := vonMangoldt_div_le_one r
    rw [criticalPrimeAtom_eq T b hr2, if_pos hr2, ← mul_sub, abs_mul, abs_of_nonneg hΛ0]
    by_cases hrR : r ≤ R
    · rw [if_pos hrR, if_pos (by omega), mul_zero, add_zero]
      have hB := abs_integral_criticalWindowWeight_dilate_sub_limit_le T b hN2 hδ0 hT
        (r := r) (K := K) (M := K * R) (by omega) (Nat.mul_le_mul_left K hrR) hsmall hlarge
      calc (ArithmeticFunction.vonMangoldt r : ℝ) / r * |_| ≤ 1 * Hd :=
            mul_le_mul hΛ1 hB (abs_nonneg _) zero_le_one
        _ = Hd := one_mul _
    · rw [if_neg hrR, if_neg (by omega), zero_add, envelopePrimeMajorant_one_eq hr2]
      have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
      set s := Real.sqrt r
      have hs0 : 0 < s := Real.sqrt_pos.mpr hr0
      have hss : s * s = r := Real.mul_self_sqrt hr0.le
      have hs1' : 1 ≤ s := Real.one_le_sqrt.mpr hr1
      have hsr : s ≤ r := by nlinarith
      have hs1 : s ≤ (r : ℝ) ^ 2 := by nlinarith
      have hcorr := abs_integral_criticalWindowWeight_dilate_le_of_window (by omega) hW2 b
        (r := r) (by omega)
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)] at hcorr
      change _ ≤ 4 / Real.pi ^ 4 * (criticalWindowConstant * (Real.sqrt 2 / s)) * E at hcorr
      have hlim := abs_correlationLimit_le T b (r := r) (by omega)
      change _ ≤ 4 / Real.pi ^ 4 * (7 / 4 * (4 * E)) / (r : ℝ) ^ 2 at hlim
      have hlim' : 4 / Real.pi ^ 4 * (7 / 4 * (4 * E)) / (r : ℝ) ^ 2 ≤
          4 / Real.pi ^ 4 * (7 * E) / s := by
        rw [show 7 / 4 * (4 * E) = 7 * E by ring]
        exact div_le_div_of_nonneg_left (by positivity) hs0 hs1
      have key : |(∫ v in Ioi 1, criticalWindowWeight v *
            (realPhaseCombination T b v * realPhaseCombination T b (r * v))) -
          factorialCriticalTranslatedCorrelationLimit T b r| ≤ Ct * E / s := by
        refine (abs_sub _ _).trans ((add_le_add hcorr (hlim.trans hlim')).trans (le_of_eq ?_))
        simp only [Ct]
        field_simp
      calc (ArithmeticFunction.vonMangoldt r : ℝ) / r * |_| ≤
            (ArithmeticFunction.vonMangoldt r : ℝ) / r * (Ct * E / s) :=
            mul_le_mul_of_nonneg_left key hΛ0
        _ = Ct * E * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r * s)) := by
          field_simp
  rw [Real.norm_eq_abs] at hb
  refine hb.trans (le_of_eq ?_)
  simp only [Hd]
  ring

/-! ### The linear window -/

/-- The head error vanishes at large scale: `G (Err_aff(K, M, N) + 6D₀/N) → 0` as `N → ∞`. -/
theorem tendsto_linearWindowHeadError_scale (K M : ℕ) (G : ℝ) :
    Tendsto (fun N : ℕ => G * (criticalWindowAffineCorrelationError K M N +
      6 * criticalWindowCosineDecay * (1 / (N : ℝ)))) atTop (𝓝 0) := by
  have ha : ∀ j : ℕ, Tendsto (fun N : ℕ => Real.pi ^ 2 * j / (140 * (N : ℝ))) atTop (𝓝 0) :=
    fun j => (tendsto_const_div_atTop_nhds_zero_nat (Real.pi ^ 2 * j / 140)).congr fun N =>
      div_div _ _ _
  have h1 := ((ha K).mul_const criticalWindowHarmonicBound).sqrt
  have h2 := ((ha M).const_mul criticalWindowHarmonicBound).sqrt
  have h3 := ((ha K).mul (ha M)).sqrt
  have h4 := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_mul
    (6 * criticalWindowCosineDecay)
  have h := (((h1.add h2).add h3).add h4).const_mul G
  simp only [zero_mul, mul_zero, Real.sqrt_zero, add_zero] at h
  exact h

/-- **The linear window of the critical prime channel.** There are `δ > 0` and `N₀` such that for
every `N ≥ N₀`, every finite family of scales in the linear window `N ≤ m + 1 ≤ (1 + δ)N` and every
real `b`, the actual critical prime channel is negative definite:
`criticalPrimeEnergy T b ≤ −(2/(7000π⁴)) Σ b_m²`.

The cutoffs are chosen in the order prime cutoff `R`, harmonic cutoff `K`, window width `δ`,
threshold `N₀`, so that `|P − P∞| ≤ (2/(7000π⁴)) Σ b²`; the limit form supplies
`P∞ ≤ −(4/(7000π⁴)) Σ b²`. -/
theorem exists_linearWindow_criticalPrimeEnergy_le :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ T : Finset ℕ,
      (∀ m ∈ T, N ≤ m + 1 ∧ ((m : ℝ) + 1) ≤ (1 + δ) * N) → ∀ b : ℕ → ℝ,
        criticalPrimeEnergy T b ≤ -(2 / (7000 * Real.pi ^ 4)) * ∑ m ∈ T, b m ^ 2 := by
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = 2 / (7000 * Real.pi ^ 4) := ⟨_, rfl⟩
  rw [← hη_def]
  have hη : 0 < η := by rw [hη_def]; positivity
  have hc4 : 0 < 4 / Real.pi ^ 4 := by positivity
  have hU := criticalWindowHarmonicBound_nonneg
  have hD := criticalWindowCosineDecay_nonneg
  have hKW := criticalWindowConstant_nonneg
  obtain ⟨W, hW_def⟩ : ∃ W : ℝ, W = ∑' k, |dyadicHarmonicWeight k| := ⟨_, rfl⟩
  have hW : 0 ≤ W := hW_def ▸ tsum_nonneg fun _ => abs_nonneg _
  obtain ⟨Ct, hCt_def⟩ : ∃ Ct : ℝ,
      Ct = 4 / Real.pi ^ 4 * (criticalWindowConstant * Real.sqrt 2 + 7) := ⟨_, rfl⟩
  -- the prime cutoff `R`
  have hτR : Tendsto (fun R => Ct * seriesTailMass (envelopePrimeMajorant 1) R) atTop (𝓝 0) := by
    have := (tendsto_seriesTailMass
      (summable_envelopePrimeMajorant_of_half_lt (by norm_num : (1 : ℝ) / 2 < 1))).const_mul Ct
    rwa [mul_zero] at this
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp (hτR.eventually_lt_const (by positivity : 0 < η / 2))
  obtain ⟨R, hR1, hRb⟩ : ∃ R : ℕ, 1 ≤ R ∧ Ct * seriesTailMass (envelopePrimeMajorant 1) R < η / 2 :=
    ⟨max R0 1, le_max_right _ _, hR0 _ (le_max_left _ _)⟩
  -- the harmonic cutoff `K`
  have hτK : Tendsto (fun K => ((R : ℝ) + 1) *
      (4 / Real.pi ^ 4 * (2 * (criticalWindowHarmonicBound + 4) * W)) *
        seriesTailMass (fun k => |dyadicHarmonicWeight k|) K) atTop (𝓝 0) := by
    have := (tendsto_seriesTailMass summable_abs_dyadicHarmonicWeight).const_mul
      (((R : ℝ) + 1) * (4 / Real.pi ^ 4 * (2 * (criticalWindowHarmonicBound + 4) * W)))
    rwa [mul_zero] at this
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp (hτK.eventually_lt_const (by positivity : 0 < η / 8))
  obtain ⟨K, hK1, hKb⟩ : ∃ K : ℕ, 1 ≤ K ∧
      ((R : ℝ) + 1) * (4 / Real.pi ^ 4 * (2 * (criticalWindowHarmonicBound + 4) * W)) *
        seriesTailMass (fun k => |dyadicHarmonicWeight k|) K < η / 8 :=
    ⟨max K0 1, le_max_right _ _, hK0 _ (le_max_left _ _)⟩
  -- the window width `δ`
  obtain ⟨G, hG_def⟩ : ∃ G : ℝ, G = ((R : ℝ) + 1) * (4 / Real.pi ^ 4) * W ^ 2 := ⟨_, rfl⟩
  have hG : 0 ≤ G := by rw [hG_def]; positivity
  have hKR : (1 : ℝ) ≤ (K : ℝ) + ((K * R : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have : (0 : ℝ) ≤ ((K * R : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨δ, hδ, hδ1, hδKR, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ((K : ℝ) + ((K * R : ℕ) : ℝ)) * δ ≤ 1 / 4 ∧
        G * (6 * criticalWindowCosineDecay) * δ ≤ η / 16 := by
    set KM := (K : ℝ) + ((K * R : ℕ) : ℝ)
    have h1 : 0 < G * criticalWindowCosineDecay + 1 := by positivity
    refine ⟨min 1 (min (1 / (4 * KM)) (η / (96 * (G * criticalWindowCosineDecay + 1)))),
      lt_min one_pos (lt_min (by positivity) (by positivity)), min_le_left _ _, ?_, ?_⟩
    · have h : min 1 (min (1 / (4 * KM)) (η / (96 * (G * criticalWindowCosineDecay + 1)))) ≤
          1 / (4 * KM) := (min_le_right _ _).trans (min_le_left _ _)
      calc KM * _ ≤ KM * (1 / (4 * KM)) := mul_le_mul_of_nonneg_left h (by linarith)
        _ = 1 / 4 := by field_simp
    · have h : min 1 (min (1 / (4 * KM)) (η / (96 * (G * criticalWindowCosineDecay + 1)))) ≤
          η / (96 * (G * criticalWindowCosineDecay + 1)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      calc G * (6 * criticalWindowCosineDecay) * _ ≤
            G * (6 * criticalWindowCosineDecay) * (η / (96 * (G * criticalWindowCosineDecay + 1))) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = η / 16 * (G * criticalWindowCosineDecay / (G * criticalWindowCosineDecay + 1)) := by
          field_simp; ring
        _ ≤ η / 16 := mul_le_of_le_one_right (by positivity) ((div_le_one h1).mpr (by linarith))
  -- the threshold `N₀`
  have hev := ((tendsto_linearWindowHeadError_scale K (K * R) G).eventually_lt_const
    (by positivity : 0 < η / 4)).and (eventually_ge_atTop (K + K * R + 2))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨δ, hδ, N₀, fun N hN T hT b => ?_⟩
  obtain ⟨hNb, hNK⟩ := hN₀ N hN
  have hN2 : 2 ≤ N := by omega
  have hlarge : (K : ℝ) + ((K * R : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : K + K * R ≤ N)
  have hT' : ∀ n ∈ T, (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ∧ ((n + 1 : ℕ) : ℝ) ≤ (1 + δ) * N :=
    fun n hn => ⟨by exact_mod_cast (hT n hn).1, by push_cast; exact (hT n hn).2⟩
  have hcmp := abs_criticalPrimeEnergy_sub_limit_le T b hN2 hδ.le hδ1 hT' hδKR hlarge
  rw [← hW_def, ← hCt_def] at hcmp
  -- the comparison error splits into the four chosen pieces
  have herr : ((R : ℝ) + 1) * (4 / Real.pi ^ 4 *
        (linearWindowHeadError K (K * R) N δ * W ^ 2 + 2 * (criticalWindowHarmonicBound + 4) * W *
          seriesTailMass (fun k => |dyadicHarmonicWeight k|) K)) +
      Ct * seriesTailMass (envelopePrimeMajorant 1) R ≤ η := by
    have e : ((R : ℝ) + 1) * (4 / Real.pi ^ 4 *
          (linearWindowHeadError K (K * R) N δ * W ^ 2 + 2 * (criticalWindowHarmonicBound + 4) * W *
            seriesTailMass (fun k => |dyadicHarmonicWeight k|) K)) +
        Ct * seriesTailMass (envelopePrimeMajorant 1) R =
        Ct * seriesTailMass (envelopePrimeMajorant 1) R +
          ((R : ℝ) + 1) * (4 / Real.pi ^ 4 * (2 * (criticalWindowHarmonicBound + 4) * W)) *
            seriesTailMass (fun k => |dyadicHarmonicWeight k|) K +
          G * (criticalWindowAffineCorrelationError K (K * R) N +
            6 * criticalWindowCosineDecay * (1 / (N : ℝ))) +
          G * (6 * criticalWindowCosineDecay) * δ := by
      rw [hG_def]
      unfold linearWindowHeadError
      ring
    rw [e]
    linarith
  have hE : 0 ≤ ∑ m ∈ T, b m ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfinal := hcmp.trans (mul_le_mul_of_nonneg_right herr hE)
  have hlim := factorialCriticalTranslatedPrimeLimit_le_neg_energy T b
  rw [show 4 / (7000 * Real.pi ^ 4) = 2 * η by rw [hη_def]; ring] at hlim
  have := le_abs_self (criticalPrimeEnergy T b - factorialCriticalTranslatedPrimeLimit T b)
  nlinarith

end GaloisForLFunctions.ArithmeticPositivityTheory
