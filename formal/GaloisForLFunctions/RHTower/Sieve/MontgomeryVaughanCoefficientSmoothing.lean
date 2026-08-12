import GaloisForLFunctions.RHTower.Sieve.TrigParseval
import GaloisForLFunctions.RHTower.Sieve.VinogradovSeparatedBlock
import GaloisForLFunctions.RHTower.Sieve.AverageBalancedDivisors
import GaloisForLFunctions.HTGeometry.BohrMultiFejerMultiplier

/-!
# Montgomery--Vaughan finite coefficient smoothing

Finite, constant-explicit versions of Lemmas 24.8 and 24.9.  The receiver later uses only finite
coefficient sequences, so no summability or compactness wrapper is needed: a uniform bound for the
full trigonometric polynomial is passed directly.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Number of divisors of `n` in the closed dyadic window `[Q,2Q]`. -/
def mvBalancedDivisorCount (Q n : ℕ) : ℕ :=
  ((Finset.Icc Q (2 * Q)).filter fun d => d ∣ n).card

/-- Local first moment of balanced divisors.  This is the boundary estimate used in MV24.9. -/
theorem sum_mvBalancedDivisorCount_Ioc_le
    {Q A B : ℕ} (hQ : 1 ≤ Q) (hAB : A ≤ B) :
    ∑ n ∈ Finset.Ioc A B, (mvBalancedDivisorCount Q n : ℝ) ≤
      2 * ((B - A : ℕ) : ℝ) + Q + 1 := by
  classical
  have hcount : ∀ n : ℕ,
      (mvBalancedDivisorCount Q n : ℝ) =
        ∑ d ∈ Finset.Icc Q (2 * Q), if d ∣ n then (1 : ℝ) else 0 := by
    intro n
    unfold mvBalancedDivisorCount
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun n _ => hcount n, Finset.sum_comm]
  have hterm : ∀ d ∈ Finset.Icc Q (2 * Q),
      ∑ n ∈ Finset.Ioc A B, (if d ∣ n then (1 : ℝ) else 0) ≤
        ((B - A : ℕ) : ℝ) / Q + 1 := by
    intro d hd
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hdpos : 0 < d := by
      rw [Finset.mem_Icc] at hd
      omega
    have hlocal := abs_card_filter_dvd_Ioc_sub_lt d A B hdpos hAB
    have hupper : (#{x ∈ Finset.Ioc A B | d ∣ x} : ℝ) ≤
        ((B : ℝ) - A) / d + 1 := by
      rw [abs_lt] at hlocal
      linarith
    have hcastSub : (((B - A : ℕ) : ℝ)) = (B : ℝ) - A := by
      simpa using (Nat.cast_sub hAB : ((B - A : ℕ) : ℝ) = (B : ℝ) - A)
    have hdQ : (Q : ℝ) ≤ d := by
      exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ)
    have hdiv : ((B : ℝ) - A) / d ≤ ((B : ℝ) - A) / Q := by
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr (by exact_mod_cast hAB))
        hQpos hdQ
    rw [hcastSub]
    exact hupper.trans (by simpa only [add_comm] using add_le_add_right hdiv 1)
  calc
    _ ≤ ∑ _d ∈ Finset.Icc Q (2 * Q),
        (((B - A : ℕ) : ℝ) / Q + 1) := Finset.sum_le_sum hterm
    _ = ((Q + 1 : ℕ) : ℝ) * ((((B - A : ℕ) : ℝ) / Q) + 1) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      congr 2
      omega
    _ ≤ 2 * ((B - A : ℕ) : ℝ) + Q + 1 := by
      have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hlen : (0 : ℝ) ≤ ((B - A : ℕ) : ℝ) := by positivity
      have hratio : (((B - A : ℕ) : ℝ) / Q) ≤ (B - A : ℕ) := by
        rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hQreal)]
        nlinarith
      have hQne : (Q : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hQreal)
      calc
        ((Q + 1 : ℕ) : ℝ) * ((((B - A : ℕ) : ℝ) / Q) + 1) =
            ((B - A : ℕ) : ℝ) + ((B - A : ℕ) : ℝ) / Q + Q + 1 := by
          push_cast
          field_simp
          ring
        _ ≤ 2 * ((B - A : ℕ) : ℝ) + Q + 1 := by linarith

/-- Classical Fejér multiplier at integer frequency `z`, with length `R`. -/
def mvFejerMultiplier (R : ℕ) (z : ℤ) : ℝ :=
  if z.natAbs < R then 1 - (z.natAbs : ℝ) / R else 0

/-- Difference of two Fejér multipliers: exactly one on `|z| ≤ M`, linearly tapering to zero
over the next `L` frequencies. -/
def mvFejerDifferenceMultiplier (M L : ℕ) (z : ℤ) : ℝ :=
  ((M + L : ℝ) / L) * mvFejerMultiplier (M + L) z -
    ((M : ℝ) / L) * mvFejerMultiplier M z

/-- Difference kernel whose Fourier multiplier is `mvFejerDifferenceMultiplier`.  The project's
`finiteFejerKernel` has mass two, hence both coefficients contain a factor `1/2`. -/
def mvFejerDifferenceKernel (M L : ℕ) (β : ℝ) : ℝ :=
  ((M + L : ℝ) / (2 * L)) * finiteFejerKernel (M + L) β -
    ((M : ℝ) / (2 * L)) * finiteFejerKernel M β

theorem mvFejerDifferenceMultiplier_eq_one
    {M L : ℕ} (hL : 0 < L) {z : ℤ} (hz : z.natAbs ≤ M) :
    mvFejerDifferenceMultiplier M L z = 1 := by
  have hzML : z.natAbs < M + L := by omega
  unfold mvFejerDifferenceMultiplier mvFejerMultiplier
  rw [if_pos hzML]
  by_cases hzM : z.natAbs < M
  · rw [if_pos hzM]
    have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
    have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hzM))
    simp only [Nat.cast_add]
    field_simp
    ring
  · rw [if_neg hzM]
    have heq : z.natAbs = M := by omega
    rw [heq]
    have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
    simp only [Nat.cast_add]
    field_simp
    ring

theorem mvFejerDifferenceMultiplier_eq_zero
    {M L : ℕ} {z : ℤ} (hz : M + L ≤ z.natAbs) :
    mvFejerDifferenceMultiplier M L z = 0 := by
  have hzM : ¬z.natAbs < M := by omega
  have hzML : ¬z.natAbs < M + L := by omega
  simp [mvFejerDifferenceMultiplier, mvFejerMultiplier, hzM, hzML]

theorem mvFejerDifferenceMultiplier_nonneg
    {M L : ℕ} (hL : 0 < L) (z : ℤ) :
    0 ≤ mvFejerDifferenceMultiplier M L z := by
  by_cases hinner : z.natAbs ≤ M
  · rw [mvFejerDifferenceMultiplier_eq_one hL hinner]
    norm_num
  · by_cases houter : M + L ≤ z.natAbs
    · rw [mvFejerDifferenceMultiplier_eq_zero houter]
    · have hzM : ¬z.natAbs < M := by omega
      have hzML : z.natAbs < M + L := by omega
      unfold mvFejerDifferenceMultiplier mvFejerMultiplier
      rw [if_pos hzML, if_neg hzM]
      have hLr : (0 : ℝ) < L := by exact_mod_cast hL
      have hzle : (z.natAbs : ℝ) ≤ (M : ℝ) + L := by
        exact_mod_cast (le_of_lt hzML)
      have heq :
          ((M + L : ℝ) / L) * (1 - (z.natAbs : ℝ) / (M + L)) =
            ((M : ℝ) + L - z.natAbs) / L := by
        field_simp
      simp only [Nat.cast_add, mul_zero, sub_zero]
      rw [heq]
      positivity

theorem mvFejerDifferenceMultiplier_le_one
    {M L : ℕ} (hL : 0 < L) (z : ℤ) :
    mvFejerDifferenceMultiplier M L z ≤ 1 := by
  by_cases hinner : z.natAbs ≤ M
  · rw [mvFejerDifferenceMultiplier_eq_one hL hinner]
  · by_cases houter : M + L ≤ z.natAbs
    · rw [mvFejerDifferenceMultiplier_eq_zero houter]
      norm_num
    · have hzM : ¬z.natAbs < M := by omega
      have hzML : z.natAbs < M + L := by omega
      unfold mvFejerDifferenceMultiplier mvFejerMultiplier
      rw [if_pos hzML, if_neg hzM]
      have hLr : (0 : ℝ) < L := by exact_mod_cast hL
      have hzlower : (M : ℝ) ≤ (z.natAbs : ℝ) := by
        exact_mod_cast (show M ≤ z.natAbs by omega)
      have hgapr : ((M : ℝ) + L - (z.natAbs : ℝ)) / L ≤ 1 := by
        rw [div_le_one hLr]
        linarith
      have heq :
          ((M + L : ℝ) / L) * (1 - (z.natAbs : ℝ) / (M + L)) =
            ((M : ℝ) + L - z.natAbs) / L := by
        field_simp
      simp only [Nat.cast_add, mul_zero, sub_zero]
      rw [heq]
      exact hgapr

theorem abs_one_sub_mvFejerDifferenceMultiplier_le_one
    {M L : ℕ} (hL : 0 < L) (z : ℤ) :
    |1 - mvFejerDifferenceMultiplier M L z| ≤ 1 := by
  have hnonneg := mvFejerDifferenceMultiplier_nonneg (M := M) hL z
  have hle := mvFejerDifferenceMultiplier_le_one (M := M) hL z
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- Orthogonality in the `finitePhaseChar` normalization. -/
theorem integral_finitePhaseChar_intCast (z : ℤ) :
    (∫ β in (0 : ℝ)..1, finitePhaseChar ((z : ℝ) * β)) =
      if z = 0 then 1 else 0 := by
  simpa [finitePhaseChar, circleFreq] using integral_circleFreq_intCast z

private theorem card_fin_difference_fibre
    {R : ℕ} (hR : 0 < R) (z : ℤ) (hz : z.natAbs < R) :
    ((Finset.univ : Finset (Fin R × Fin R)).filter
        fun p => ((p.2.val : ℤ) - (p.1.val : ℤ)) = z).card = R - z.natAbs := by
  classical
  have hsource := GaloisForLFunctions.card_fejerFibre (R - 1) z (by omega)
  have hcard :
      ((Finset.univ : Finset (Fin R × Fin R)).filter
          fun p => ((p.2.val : ℤ) - (p.1.val : ℤ)) = z).card =
        ((Finset.range R ×ˢ Finset.range R).filter
          fun p : ℕ × ℕ => ((p.2 : ℤ) - (p.1 : ℤ)) = z).card := by
    refine Finset.card_bij (fun p _ => (p.1.val, p.2.val)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_univ, true_and] at hp ⊢
      exact ⟨⟨p.1.isLt, p.2.isLt⟩, hp⟩
    · intro p₁ _ p₂ _ hp
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst hp
      · exact congrArg Prod.snd hp
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      refine ⟨(⟨p.1, hp.1.1⟩, ⟨p.2, hp.1.2⟩), ?_, rfl⟩
      simpa using hp.2
  rw [hcard]
  have hRone : R - 1 + 1 = R := by omega
  simpa [hRone] using hsource

/-- Exact mass of the project's twice-classical Fejér kernel. -/
theorem integral_finiteFejerKernel {R : ℕ} (hR : 0 < R) :
    (∫ β in (0 : ℝ)..1, finiteFejerKernel R β) = 2 := by
  have hparseval := integral_normSq_expSum R (fun _ => (1 : ℂ))
  have hsum : (∑ _n : Fin R, ‖(1 : ℂ)‖ ^ 2) = (R : ℝ) := by simp
  rw [hsum] at hparseval
  unfold finiteFejerKernel
  rw [intervalIntegral.integral_const_mul]
  have hfun : (fun x : ℝ => Complex.normSq (finitePhaseProgression R x)) =
      fun x : ℝ => ‖expSum R (fun _ => (1 : ℂ)) x‖ ^ 2 := by
    funext x
    rw [finitePhaseProgression_eq_expSum_one, Complex.normSq_eq_norm_sq]
  rw [hfun, hparseval]
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
  field_simp

/-- Pointwise `L¹` majorant for the difference kernel. -/
theorem abs_mvFejerDifferenceKernel_le
    {M L : ℕ} (hL : 0 < L) (β : ℝ) :
    |mvFejerDifferenceKernel M L β| ≤
      ((M + L : ℝ) / (2 * L)) * finiteFejerKernel (M + L) β +
        ((M : ℝ) / (2 * L)) * finiteFejerKernel M β := by
  unfold mvFejerDifferenceKernel
  have ha : 0 ≤ ((M + L : ℝ) / (2 * L)) * finiteFejerKernel (M + L) β := by
    exact mul_nonneg (by positivity) (finiteFejerKernel_nonneg _ _)
  have hb : 0 ≤ ((M : ℝ) / (2 * L)) * finiteFejerKernel M β := by
    exact mul_nonneg (by positivity) (finiteFejerKernel_nonneg _ _)
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- Exact `L¹` cost of coefficient smoothing. -/
theorem integral_abs_mvFejerDifferenceKernel_le
    {M L : ℕ} (hL : 0 < L) :
    (∫ β in (0 : ℝ)..1, |mvFejerDifferenceKernel M L β|) ≤
      2 * (M : ℝ) / L + 1 := by
  have hML : 0 < M + L := by omega
  have hcontFejer : ∀ R : ℕ, Continuous (finiteFejerKernel R) := by
    intro R
    unfold finiteFejerKernel finitePhaseProgression finitePhaseChar
    fun_prop
  have hcontDiff : Continuous (mvFejerDifferenceKernel M L) := by
    unfold mvFejerDifferenceKernel
    exact (continuous_const.mul (hcontFejer (M + L))).sub
      (continuous_const.mul (hcontFejer M))
  have hcontAbs : Continuous fun β : ℝ => |mvFejerDifferenceKernel M L β| :=
    hcontDiff.abs
  have hcontMaj : Continuous fun β : ℝ =>
      ((M + L : ℝ) / (2 * L)) * finiteFejerKernel (M + L) β +
        ((M : ℝ) / (2 * L)) * finiteFejerKernel M β := by
    exact (continuous_const.mul (hcontFejer (M + L))).add
      (continuous_const.mul (hcontFejer M))
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num)
    (hcontAbs.intervalIntegrable 0 1) (hcontMaj.intervalIntegrable 0 1)
    (fun β _ => abs_mvFejerDifferenceKernel_le hL β)
  refine hmono.trans_eq ?_
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_finiteFejerKernel hML]
  by_cases hM : M = 0
  · subst M
    have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
    norm_num
    field_simp
  · rw [integral_finiteFejerKernel (Nat.pos_of_ne_zero hM)]
    have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
    push_cast
    field_simp
    ring
  · exact ((hcontFejer (M + L)).intervalIntegrable 0 1).const_mul _
  · exact ((hcontFejer M).intervalIntegrable 0 1).const_mul _

/-- Trigonometric polynomial after shifting frequency origin to an integer `H`. -/
def mvShiftedTrigSum (K : ℕ) (c : Fin K → ℂ) (H : ℤ) (β : ℝ) : ℂ :=
  ∑ n : Fin K, c n *
    finitePhaseChar (((n.val : ℤ) - H : ℤ) * β)

/-- Unshifted full trigonometric polynomial. -/
def mvTrigSum (K : ℕ) (c : Fin K → ℂ) (β : ℝ) : ℂ :=
  ∑ n : Fin K, c n * finitePhaseChar ((n.val : ℝ) * β)

theorem mvShiftedTrigSum_eq_phase_mul
    (K : ℕ) (c : Fin K → ℂ) (H : ℤ) (β : ℝ) :
    mvShiftedTrigSum K c H β =
      finitePhaseChar (-(H : ℝ) * β) * mvTrigSum K c β := by
  unfold mvShiftedTrigSum mvTrigSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  calc
    c n * finitePhaseChar (((n.val : ℤ) - H : ℤ) * β) =
        c n * (finitePhaseChar (-(H : ℝ) * β) *
          finitePhaseChar ((n.val : ℝ) * β)) := by
      rw [← finitePhaseChar_add]
      congr 2
      push_cast
      ring
    _ = finitePhaseChar (-(H : ℝ) * β) *
        (c n * finitePhaseChar ((n.val : ℝ) * β)) := by ring

theorem norm_mvShiftedTrigSum_eq
    (K : ℕ) (c : Fin K → ℂ) (H : ℤ) (β : ℝ) :
    ‖mvShiftedTrigSum K c H β‖ = ‖mvTrigSum K c β‖ := by
  rw [mvShiftedTrigSum_eq_phase_mul, norm_mul, norm_finitePhaseChar, one_mul]

theorem continuous_finitePhaseChar_intMul (z : ℤ) :
    Continuous fun β : ℝ => finitePhaseChar ((z : ℝ) * β) := by
  unfold finitePhaseChar
  fun_prop

theorem continuous_mvShiftedTrigSum (K : ℕ) (c : Fin K → ℂ) (H : ℤ) :
    Continuous (mvShiftedTrigSum K c H) := by
  unfold mvShiftedTrigSum
  apply continuous_finset_sum
  intro n _
  exact continuous_const.mul (continuous_finitePhaseChar_intMul ((n.val : ℤ) - H))

private theorem integral_mvShiftedTrigSum_mul_finiteFejerKernel_raw
    {K R : ℕ} (c : Fin K → ℂ) (H : ℤ) :
    (∫ β in (0 : ℝ)..1,
        mvShiftedTrigSum K c H β * (finiteFejerKernel R (-β) : ℂ)) =
      ∑ n : Fin K, ∑ uv : Fin R × Fin R,
        c n * ((2 / (R : ℝ) : ℝ) : ℂ) *
          (if ((n.val : ℤ) - H) + ((uv.2.val : ℤ) - uv.1.val) = 0
            then 1 else 0) := by
  classical
  have hfun : (fun β : ℝ =>
      mvShiftedTrigSum K c H β * (finiteFejerKernel R (-β) : ℂ)) =
      fun β : ℝ => ∑ n : Fin K, ∑ uv : Fin R × Fin R,
        c n * ((2 / (R : ℝ) : ℝ) : ℂ) *
          finitePhaseChar (((((n.val : ℤ) - H) +
            ((uv.2.val : ℤ) - uv.1.val) : ℤ) : ℝ) * β) := by
    funext β
    unfold mvShiftedTrigSum
    rw [finiteFejerKernel_expansion, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro uv _
    calc
      c n * finitePhaseChar (((n.val : ℤ) - H : ℤ) * β) *
          (((2 / (R : ℝ) : ℝ) : ℂ) *
            finitePhaseChar ((((uv.1.val : ℝ) - uv.2.val) * -β))) =
        c n * ((2 / (R : ℝ) : ℝ) : ℂ) *
          (finitePhaseChar (((n.val : ℤ) - H : ℤ) * β) *
            finitePhaseChar ((((uv.1.val : ℝ) - uv.2.val) * -β))) := by ring
      _ = _ := by
        rw [← finitePhaseChar_add]
        congr 1
        push_cast
        ring
  rw [hfun, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro uv _
      rw [intervalIntegral.integral_const_mul,
        integral_finitePhaseChar_intCast]
    · intro uv _
      exact Continuous.intervalIntegrable (μ := volume) ((continuous_finitePhaseChar_intMul
        (((n.val : ℤ) - H) + ((uv.2.val : ℤ) - uv.1.val))).const_mul _) 0 1
  · intro n _
    apply Continuous.intervalIntegrable
    apply continuous_finset_sum
    intro uv _
    exact (continuous_finitePhaseChar_intMul
      (((n.val : ℤ) - H) + ((uv.2.val : ℤ) - uv.1.val))).const_mul _

private theorem sum_finPair_orthogonality_eq_multiplier
    {R : ℕ} (hR : 0 < R) (z : ℤ) :
    (∑ uv : Fin R × Fin R,
        (if z + ((uv.2.val : ℤ) - uv.1.val) = 0 then (1 : ℂ) else 0)) =
      ((R : ℝ) * mvFejerMultiplier R z : ℝ) := by
  classical
  by_cases hz : z.natAbs < R
  · have hcard := card_fin_difference_fibre hR (-z) (by simpa using hz)
    have hfilter :
        ((Finset.univ : Finset (Fin R × Fin R)).filter
          fun uv => z + ((uv.2.val : ℤ) - uv.1.val) = 0) =
        ((Finset.univ : Finset (Fin R × Fin R)).filter
          fun uv => ((uv.2.val : ℤ) - uv.1.val) = -z) := by
      ext uv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul, hcard]
    simp only [mvFejerMultiplier, if_pos hz, Complex.ofReal_mul, Complex.ofReal_natCast]
    have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
    have hreal : ((R - z.natAbs : ℕ) : ℝ) =
        (R : ℝ) * (1 - (z.natAbs : ℝ) / R) := by
      rw [Nat.cast_sub (le_of_lt hz)]
      field_simp
    simpa [Int.natAbs_neg] using congrArg (fun r : ℝ => (r : ℂ)) hreal
  · have hempty :
        ((Finset.univ : Finset (Fin R × Fin R)).filter
          fun uv => z + ((uv.2.val : ℤ) - uv.1.val) = 0) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro uv _ huv
      have huvAbs : (((uv.2.val : ℤ) - uv.1.val)).natAbs < R := by
        have h₁ : uv.1.val < R := uv.1.isLt
        have h₂ : uv.2.val < R := uv.2.isLt
        omega
      have : z.natAbs < R := by
        have heq : ((uv.2.val : ℤ) - uv.1.val) = -z := by omega
        simpa [heq] using huvAbs
      exact hz this
    rw [← Finset.sum_filter, hempty]
    simp [mvFejerMultiplier, hz]

/-- Fourier multiplier of the twice-classical Fejér kernel. -/
theorem integral_mvShiftedTrigSum_mul_finiteFejerKernel
    {K R : ℕ} (hR : 0 < R) (c : Fin K → ℂ) (H : ℤ) :
    (∫ β in (0 : ℝ)..1,
        mvShiftedTrigSum K c H β * (finiteFejerKernel R (-β) : ℂ)) =
      ∑ n : Fin K, c n *
        ((2 * mvFejerMultiplier R ((n.val : ℤ) - H) : ℝ) : ℂ) := by
  rw [integral_mvShiftedTrigSum_mul_finiteFejerKernel_raw]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.mul_sum]
  rw [sum_finPair_orthogonality_eq_multiplier hR]
  push_cast
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
  field_simp [hRc]

/-- Fourier multiplier of the Fejér difference kernel. -/
theorem integral_mvShiftedTrigSum_mul_differenceKernel
    {K M L : ℕ} (hM : 0 < M) (hL : 0 < L) (c : Fin K → ℂ) (H : ℤ) :
    (∫ β in (0 : ℝ)..1,
        mvShiftedTrigSum K c H β * (mvFejerDifferenceKernel M L (-β) : ℂ)) =
      ∑ n : Fin K, c n *
        (mvFejerDifferenceMultiplier M L ((n.val : ℤ) - H) : ℂ) := by
  have hML : 0 < M + L := by omega
  let A : ℂ := (((M + L : ℝ) / (2 * L) : ℝ) : ℂ)
  let D : ℂ := (((M : ℝ) / (2 * L) : ℝ) : ℂ)
  have hfun : (fun β : ℝ =>
      mvShiftedTrigSum K c H β * (mvFejerDifferenceKernel M L (-β) : ℂ)) =
      fun β : ℝ => A *
          (mvShiftedTrigSum K c H β * (finiteFejerKernel (M + L) (-β) : ℂ)) -
        D * (mvShiftedTrigSum K c H β * (finiteFejerKernel M (-β) : ℂ)) := by
    funext β
    unfold mvFejerDifferenceKernel A D
    push_cast
    ring
  have hcontFejer : ∀ R : ℕ, Continuous (fun β : ℝ => (finiteFejerKernel R (-β) : ℂ)) := by
    intro R
    unfold finiteFejerKernel finitePhaseProgression finitePhaseChar
    fun_prop
  have hcontShift := continuous_mvShiftedTrigSum K c H
  have hint₁ : IntervalIntegrable (fun β : ℝ =>
      A * (mvShiftedTrigSum K c H β * (finiteFejerKernel (M + L) (-β) : ℂ)))
      volume 0 1 :=
    (continuous_const.mul (hcontShift.mul (hcontFejer (M + L)))).intervalIntegrable 0 1
  have hint₂ : IntervalIntegrable (fun β : ℝ =>
      D * (mvShiftedTrigSum K c H β * (finiteFejerKernel M (-β) : ℂ)))
      volume 0 1 :=
    (continuous_const.mul (hcontShift.mul (hcontFejer M))).intervalIntegrable 0 1
  rw [hfun, intervalIntegral.integral_sub hint₁ hint₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_mvShiftedTrigSum_mul_finiteFejerKernel hML,
    integral_mvShiftedTrigSum_mul_finiteFejerKernel hM,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  unfold A D mvFejerDifferenceMultiplier
  push_cast
  ring

/-- Symmetric coefficient sum around integer center `H`. -/
def mvCenteredCoefficientSum (K : ℕ) (c : Fin K → ℂ) (H : ℤ) (M : ℕ) : ℂ :=
  ∑ n : Fin K, c n *
    if (((n.val : ℤ) - H).natAbs ≤ M) then 1 else 0

/-- `ℓ¹` mass in the two boundary annuli of total width `2L`. -/
def mvBoundaryCoefficientMass
    (K : ℕ) (c : Fin K → ℂ) (H : ℤ) (M L : ℕ) : ℝ :=
  ∑ n : Fin K,
    if M < (((n.val : ℤ) - H).natAbs) ∧
        (((n.val : ℤ) - H).natAbs) < M + L then ‖c n‖ else 0

private theorem norm_indicator_sub_differenceMultiplier_le_boundary
    {M L : ℕ} (hL : 0 < L) (z : ℤ) :
    ‖((if z.natAbs ≤ M then (1 : ℂ) else 0) -
        (mvFejerDifferenceMultiplier M L z : ℂ))‖ ≤
      if M < z.natAbs ∧ z.natAbs < M + L then 1 else 0 := by
  by_cases hinner : z.natAbs ≤ M
  · rw [if_pos hinner, mvFejerDifferenceMultiplier_eq_one hL hinner]
    rw [if_neg (by omega)]
    norm_num
  · by_cases houter : M + L ≤ z.natAbs
    · rw [if_neg hinner, mvFejerDifferenceMultiplier_eq_zero houter]
      rw [if_neg (by omega)]
      norm_num
    · have hboundary : M < z.natAbs ∧ z.natAbs < M + L := by omega
      rw [if_neg hinner, if_pos hboundary, zero_sub, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (mvFejerDifferenceMultiplier_nonneg hL z)]
      exact mvFejerDifferenceMultiplier_le_one hL z

private theorem norm_centered_sub_weighted_le_boundary
    {K M L : ℕ} (hL : 0 < L) (c : Fin K → ℂ) (H : ℤ) :
    ‖mvCenteredCoefficientSum K c H M -
        ∑ n : Fin K, c n *
          (mvFejerDifferenceMultiplier M L ((n.val : ℤ) - H) : ℂ)‖ ≤
      mvBoundaryCoefficientMass K c H M L := by
  rw [mvCenteredCoefficientSum, ← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ n : Fin K, c n *
        (((if (((n.val : ℤ) - H).natAbs ≤ M) then (1 : ℂ) else 0) -
          (mvFejerDifferenceMultiplier M L ((n.val : ℤ) - H) : ℂ)))‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ ∑ n : Fin K, ‖c n *
        (((if (((n.val : ℤ) - H).natAbs ≤ M) then (1 : ℂ) else 0) -
          (mvFejerDifferenceMultiplier M L ((n.val : ℤ) - H) : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ mvBoundaryCoefficientMass K c H M L := by
      unfold mvBoundaryCoefficientMass
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul]
      have hpoint := norm_indicator_sub_differenceMultiplier_le_boundary
        (M := M) hL ((n.val : ℤ) - H)
      by_cases hb : M < (((n.val : ℤ) - H).natAbs) ∧
          (((n.val : ℤ) - H).natAbs) < M + L
      · rw [if_pos hb] at hpoint ⊢
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hpoint (norm_nonneg (c n))
      · rw [if_neg hb] at hpoint ⊢
        have hz : ‖((if (((n.val : ℤ) - H).natAbs ≤ M) then (1 : ℂ) else 0) -
            (mvFejerDifferenceMultiplier M L ((n.val : ℤ) - H) : ℂ))‖ = 0 :=
          le_antisymm hpoint (norm_nonneg _)
        rw [hz, mul_zero]

/-- **Montgomery--Vaughan Lemma 24.8, finite exact form.** -/
theorem norm_mvCenteredCoefficientSum_le
    {K M L : ℕ} (hM : 0 < M) (hL : 0 < L)
    (c : Fin K → ℂ) (H : ℤ) {S : ℝ} (hS : 0 ≤ S)
    (hfull : ∀ β : ℝ, ‖mvShiftedTrigSum K c H β‖ ≤ S) :
    ‖mvCenteredCoefficientSum K c H M‖ ≤
      (2 * (M : ℝ) / L + 1) * S + mvBoundaryCoefficientMass K c H M L := by
  let W : ℂ := ∑ n : Fin K, c n *
    (mvFejerDifferenceMultiplier M L ((n.val : ℤ) - H) : ℂ)
  have hidentity : W = (∫ β in (0 : ℝ)..1,
      mvShiftedTrigSum K c H β * (mvFejerDifferenceKernel M L (-β) : ℂ)) := by
    exact (integral_mvShiftedTrigSum_mul_differenceKernel hM hL c H).symm
  have hcontKernel : Continuous (mvFejerDifferenceKernel M L) := by
    unfold mvFejerDifferenceKernel finiteFejerKernel finitePhaseProgression finitePhaseChar
    fun_prop
  have hcontNorm : Continuous fun β : ℝ =>
      ‖mvShiftedTrigSum K c H β * (mvFejerDifferenceKernel M L (-β) : ℂ)‖ :=
    ((continuous_mvShiftedTrigSum K c H).mul
      (Complex.continuous_ofReal.comp (hcontKernel.comp continuous_neg))).norm
  have hcontMaj : Continuous fun β : ℝ => S * |mvFejerDifferenceKernel M L (-β)| :=
    continuous_const.mul ((hcontKernel.comp continuous_neg).abs)
  have hpoint : ∀ β : ℝ,
      ‖mvShiftedTrigSum K c H β * (mvFejerDifferenceKernel M L (-β) : ℂ)‖ ≤
        S * |mvFejerDifferenceKernel M L (-β)| := by
    intro β
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hfull β) (abs_nonneg _)
  have hintegralPoint := intervalIntegral.integral_mono_on (μ := volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num)
    (hcontNorm.intervalIntegrable 0 1) (hcontMaj.intervalIntegrable 0 1)
    (fun β _ => hpoint β)
  have hkernelNeg :
      (∫ β in (0 : ℝ)..1, |mvFejerDifferenceKernel M L (-β)|) =
        ∫ β in (0 : ℝ)..1, |mvFejerDifferenceKernel M L β| := by
    have heven : ∀ β : ℝ, mvFejerDifferenceKernel M L (-β) =
        mvFejerDifferenceKernel M L β := by
      intro β
      unfold mvFejerDifferenceKernel
      rw [finiteFejerKernel_neg, finiteFejerKernel_neg]
    exact intervalIntegral.integral_congr (fun β _ => by rw [heven β])
  have hW : ‖W‖ ≤ (2 * (M : ℝ) / L + 1) * S := by
    rw [hidentity]
    calc
      _ ≤ ∫ β in (0 : ℝ)..1,
          ‖mvShiftedTrigSum K c H β *
            (mvFejerDifferenceKernel M L (-β) : ℂ)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ β in (0 : ℝ)..1, S * |mvFejerDifferenceKernel M L (-β)| :=
        hintegralPoint
      _ = S * (∫ β in (0 : ℝ)..1, |mvFejerDifferenceKernel M L β|) := by
        rw [intervalIntegral.integral_const_mul, hkernelNeg]
      _ ≤ S * (2 * (M : ℝ) / L + 1) := by
        exact mul_le_mul_of_nonneg_left
          (integral_abs_mvFejerDifferenceKernel_le hL) hS
      _ = (2 * (M : ℝ) / L + 1) * S := by ring
  have hboundary := norm_centered_sub_weighted_le_boundary (M := M) hL c H
  have htriangle : ‖mvCenteredCoefficientSum K c H M‖ ≤
      ‖W‖ + ‖mvCenteredCoefficientSum K c H M - W‖ :=
    norm_le_norm_add_norm_sub' _ _
  exact htriangle.trans (add_le_add hW (by simpa [W] using hboundary))

/-- Arithmetic control of the two smoothing annuli by balanced-divisor multiplicity. -/
theorem mvBoundaryCoefficientMass_le
    {K Q H M L : ℕ} (hQ : 1 ≤ Q) (hM : 0 < M) (hL : 0 < L)
    (hMLH : M + L ≤ H)
    (hHK : H + M + L ≤ K) (c : Fin K → ℂ)
    (hc : ∀ n : Fin K, ‖c n‖ ≤ mvBalancedDivisorCount Q n.val) :
    mvBoundaryCoefficientMass K c (H : ℤ) M L ≤
      4 * (L : ℝ) + 2 * Q + 2 := by
  let g : ℕ → ℝ := fun n => mvBalancedDivisorCount Q n
  let left : Finset ℕ := Finset.Ioc (H - (M + L)) (H - M)
  let right : Finset ℕ := Finset.Ioc (H + M) (H + M + L - 1)
  have hHleK : H ≤ K := by omega
  have hleftSubset : left ⊆ Finset.range K := by
    intro n hn
    change n ∈ Finset.Ioc (H - (M + L)) (H - M) at hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_range]
    omega
  have hrightSubset : right ⊆ Finset.range K := by
    intro n hn
    change n ∈ Finset.Ioc (H + M) (H + M + L - 1) at hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_range]
    omega
  have hfilterLeft : (Finset.range K).filter (fun n => n ∈ left) = left := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · exact fun hn => hn.2
    · exact fun hn => ⟨hleftSubset hn, hn⟩
  have hfilterRight : (Finset.range K).filter (fun n => n ∈ right) = right := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · exact fun hn => hn.2
    · exact fun hn => ⟨hrightSubset hn, hn⟩
  rw [mvBoundaryCoefficientMass, Finset.sum_fin_eq_sum_range]
  have hpoint : ∀ (n : ℕ) (hn : n ∈ Finset.range K),
      (if M < (((n : ℤ) - (H : ℤ)).natAbs) ∧
          (((n : ℤ) - (H : ℤ)).natAbs) < M + L
        then ‖c ⟨n, Finset.mem_range.mp hn⟩‖ else 0) ≤
        (if n ∈ left then g n else 0) + (if n ∈ right then g n else 0) := by
    intro n hn
    have hnK : n < K := Finset.mem_range.mp hn
    by_cases hb : M < (((n : ℤ) - (H : ℤ)).natAbs) ∧
        (((n : ℤ) - (H : ℤ)).natAbs) < M + L
    · rw [if_pos hb]
      have hcg : ‖c ⟨n, hnK⟩‖ ≤ g n := by
        simpa [g] using hc ⟨n, hnK⟩
      rcases le_or_gt n H with hnH | hHn
      · have hnleft : n ∈ left := by
          change n ∈ Finset.Ioc (H - (M + L)) (H - M)
          rw [Finset.mem_Ioc]
          constructor <;> omega
        rw [if_pos hnleft]
        exact hcg.trans (le_add_of_nonneg_right (by positivity))
      · have hnright : n ∈ right := by
          change n ∈ Finset.Ioc (H + M) (H + M + L - 1)
          rw [Finset.mem_Ioc]
          constructor <;> omega
        rw [if_pos hnright]
        exact hcg.trans (le_add_of_nonneg_left (by positivity))
    · rw [if_neg hb]
      positivity
  calc
    _ ≤ ∑ n ∈ Finset.range K,
        ((if n ∈ left then g n else 0) + (if n ∈ right then g n else 0)) := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [dif_pos (Finset.mem_range.mp hn)]
      exact hpoint n hn
    _ = (∑ n ∈ left, g n) + ∑ n ∈ right, g n := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [← Finset.sum_filter, hfilterLeft]
      · rw [← Finset.sum_filter, hfilterRight]
    _ ≤ (2 * (((H - M) - (H - (M + L)) : ℕ) : ℝ) + Q + 1) +
          (2 * (((H + M + L - 1) - (H + M) : ℕ) : ℝ) + Q + 1) := by
      exact add_le_add
        (sum_mvBalancedDivisorCount_Ioc_le hQ (by omega))
        (sum_mvBalancedDivisorCount_Ioc_le hQ (by omega))
    _ ≤ 4 * (L : ℝ) + 2 * Q + 2 := by
      have hleftLen : (H - M) - (H - (M + L)) = L := by omega
      have hrightLen : H + M + L - 1 - (H + M) = L - 1 := by omega
      rw [hleftLen, hrightLen]
      have hcast : (((L - 1 : ℕ) : ℝ)) ≤ (L : ℝ) := by exact_mod_cast (Nat.sub_le L 1)
      push_cast
      linarith

/-- MV24.8 plus balanced-divisor annulus accounting. -/
theorem norm_mvCenteredCoefficientSum_le_of_balancedDivisors
    {K Q H M L : ℕ} (hQ : 1 ≤ Q) (hM : 0 < M) (hL : 0 < L)
    (hMLH : M + L ≤ H) (hHK : H + M + L ≤ K)
    (c : Fin K → ℂ)
    (hc : ∀ n : Fin K, ‖c n‖ ≤ mvBalancedDivisorCount Q n.val)
    {S : ℝ} (hS : 0 ≤ S) (hfull : ∀ β : ℝ, ‖mvTrigSum K c β‖ ≤ S) :
    ‖mvCenteredCoefficientSum K c (H : ℤ) M‖ ≤
      (2 * (M : ℝ) / L + 1) * S + (4 * (L : ℝ) + 2 * Q + 2) := by
  have hsmooth := norm_mvCenteredCoefficientSum_le hM hL c (H : ℤ) hS
    (fun β => by simpa [norm_mvShiftedTrigSum_eq] using hfull β)
  have hboundary := mvBoundaryCoefficientMass_le hQ hM hL hMLH hHK c hc
  linarith

/-- Coefficient sum on the natural interval `(Y,Z]`. -/
def mvIntervalCoefficientSum (K : ℕ) (c : Fin K → ℂ) (Y Z : ℕ) : ℂ :=
  ∑ n : Fin K, c n * if Y < n.val ∧ n.val ≤ Z then 1 else 0

private theorem midpoint_radius_geometry
    {Y Z : ℕ} (hYZ : Y ≤ Z) :
    let H := (Y + Z + 1) / 2
    let M := (Z - Y) / 2
    H + M = Z ∧ Y ≤ H - M := by
  omega

private theorem midpoint_indicator_eq_of_ne_left
    {Y Z n : ℕ} (hYZ : Y ≤ Z) (hnY : n ≠ Y) :
    (((n : ℤ) - (((Y + Z + 1) / 2 : ℕ) : ℤ)).natAbs ≤ (Z - Y) / 2) ↔
      Y < n ∧ n ≤ Z := by
  omega

/-- Midpoint symmetrization changes `(Y,Z]` by at most its left endpoint. -/
theorem norm_mvIntervalCoefficientSum_le_midpoint
    {K Y Z : ℕ} (hYZ : Y ≤ Z) (hYK : Y < K)
    (c : Fin K → ℂ) :
    ‖mvIntervalCoefficientSum K c Y Z‖ ≤
      ‖mvCenteredCoefficientSum K c (((Y + Z + 1) / 2 : ℕ) : ℤ)
        ((Z - Y) / 2)‖ + ‖c ⟨Y, hYK⟩‖ := by
  let y : Fin K := ⟨Y, hYK⟩
  let H : ℕ := (Y + Z + 1) / 2
  let M : ℕ := (Z - Y) / 2
  have hdiff : ‖mvIntervalCoefficientSum K c Y Z -
      mvCenteredCoefficientSum K c (H : ℤ) M‖ ≤ ‖c y‖ := by
    rw [mvIntervalCoefficientSum, mvCenteredCoefficientSum,
      ← Finset.sum_sub_distrib]
    let F : Fin K → ℂ := fun n =>
      (c n * (if Y < n.val ∧ n.val ≤ Z then 1 else 0)) -
        c n * (if (((n.val : ℤ) - (H : ℤ)).natAbs ≤ M) then 1 else 0)
    have hsum : (∑ n : Fin K, F n) = F y := by
      apply Finset.sum_eq_single y
      · intro n _ hn
        have hnval : n.val ≠ Y := by
          intro heq
          apply hn
          apply Fin.ext
          simpa [y] using heq
        have hiff := midpoint_indicator_eq_of_ne_left hYZ hnval
        by_cases hi : Y < n.val ∧ n.val ≤ Z
        · dsimp [F]
          rw [if_pos hi, if_pos (hiff.mpr hi)]
          ring
        · dsimp [F]
          rw [if_neg hi, if_neg (fun h => hi (hiff.mp h))]
          ring
      · intro hy
        exact False.elim (hy (Finset.mem_univ y))
    change ‖∑ n : Fin K, F n‖ ≤ ‖c y‖
    rw [hsum]
    dsimp [F]
    calc
      _ = ‖c y‖ *
          ‖(if Y < y.val ∧ y.val ≤ Z then (1 : ℂ) else 0) -
            (if (((y.val : ℤ) - (H : ℤ)).natAbs ≤ M) then (1 : ℂ) else 0)‖ := by
        rw [← norm_mul]
        congr 1
        ring
      _ ≤ ‖c y‖ * 1 := by
        gcongr
        split_ifs <;> simp
      _ = ‖c y‖ := mul_one _
  have htriangle : ‖mvIntervalCoefficientSum K c Y Z‖ ≤
      ‖mvCenteredCoefficientSum K c (H : ℤ) M‖ +
        ‖mvIntervalCoefficientSum K c Y Z -
          mvCenteredCoefficientSum K c (H : ℤ) M‖ :=
    norm_le_norm_add_norm_sub' _ _
  have := htriangle.trans (add_le_add (le_refl _) hdiff)
  simpa [H, M, y] using this

/-- Finite explicit MV24.9 before optimizing smoothing length `L`. -/
theorem norm_mvIntervalCoefficientSum_le_of_balancedDivisors
    {K Q Y Z L : ℕ} (hQ : 1 ≤ Q) (hYZ : Y ≤ Z) (hYK : Y < K)
    (hwidth : 2 ≤ Z - Y) (hL : 0 < L) (hLY : L ≤ Y) (hZLK : Z + L ≤ K)
    (c : Fin K → ℂ)
    (hc : ∀ n : Fin K, ‖c n‖ ≤ mvBalancedDivisorCount Q n.val)
    {S : ℝ} (hS : 0 ≤ S) (hfull : ∀ β : ℝ, ‖mvTrigSum K c β‖ ≤ S) :
    ‖mvIntervalCoefficientSum K c Y Z‖ ≤
      (2 * (((Z - Y) / 2 : ℕ) : ℝ) / L + 1) * S +
        (4 * (L : ℝ) + 3 * Q + 3) := by
  let H : ℕ := (Y + Z + 1) / 2
  let M : ℕ := (Z - Y) / 2
  have hM : 0 < M := by omega
  have hgeom := midpoint_radius_geometry hYZ
  dsimp only at hgeom
  have hMLH : M + L ≤ H := by omega
  have hHK : H + M + L ≤ K := by omega
  have hmid := norm_mvIntervalCoefficientSum_le_midpoint hYZ hYK c
  have hcentre := norm_mvCenteredCoefficientSum_le_of_balancedDivisors
    hQ hM hL hMLH hHK c hc hS hfull
  have hendpoint : ‖c ⟨Y, hYK⟩‖ ≤ ((Q + 1 : ℕ) : ℝ) := by
    have hcY := hc ⟨Y, hYK⟩
    have hcard : mvBalancedDivisorCount Q Y ≤ Q + 1 := by
      unfold mvBalancedDivisorCount
      calc
        _ ≤ (Finset.Icc Q (2 * Q)).card := Finset.card_filter_le _ _
        _ = Q + 1 := by rw [Nat.card_Icc]; omega
    exact hcY.trans (by exact_mod_cast hcard)
  have hendpoint' : ‖c ⟨Y, hYK⟩‖ ≤ (Q : ℝ) + 1 := by
    simpa using hendpoint
  dsimp only [H, M] at hmid hcentre ⊢
  linarith [hendpoint']

/-- Square-root smoothing length used in MV24.9. -/
def mvOptimalSmoothingLength (A : ℕ) (S : ℝ) : ℕ :=
  max 1 ⌈Real.sqrt ((A : ℝ) * S)⌉₊

/-- **Montgomery--Vaughan Lemma 24.9, finite explicit square-root form.** -/
theorem norm_mvIntervalCoefficientSum_le_sqrt
    {K Q A Y Z : ℕ} (hQ : 1 ≤ Q) (hA : 1 ≤ A)
    (hYZ : Y ≤ Z) (hYK : Y < K) (hwidthLower : 2 ≤ Z - Y)
    (hwidthUpper : Z - Y ≤ A) (hAY : A ≤ Y) (hZAK : Z + A ≤ K)
    (c : Fin K → ℂ)
    (hc : ∀ n : Fin K, ‖c n‖ ≤ mvBalancedDivisorCount Q n.val)
    {S : ℝ} (hS : 0 ≤ S) (hSA : S ≤ A)
    (hfull : ∀ β : ℝ, ‖mvTrigSum K c β‖ ≤ S) :
    ‖mvIntervalCoefficientSum K c Y Z‖ ≤
      7 * Real.sqrt ((A : ℝ) * S) + 3 * Q + 7 := by
  let r : ℝ := Real.sqrt ((A : ℝ) * S)
  let L : ℕ := mvOptimalSmoothingLength A S
  have hAS : 0 ≤ (A : ℝ) * S := mul_nonneg (by positivity) hS
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrA : r ≤ (A : ℝ) := by
    dsimp [r]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hAr : (0 : ℝ) ≤ A := by positivity
      nlinarith
  have hceilA : ⌈r⌉₊ ≤ A := Nat.ceil_le.mpr hrA
  have hL : 0 < L := by unfold L mvOptimalSmoothingLength; omega
  have hLA : L ≤ A := by
    unfold L mvOptimalSmoothingLength
    simpa only [r] using max_le hA hceilA
  have hrL : r ≤ (L : ℝ) := by
    unfold L mvOptimalSmoothingLength
    rw [Nat.cast_max]
    exact (Nat.le_ceil r).trans (le_max_right _ _)
  have hLupper : (L : ℝ) ≤ r + 1 := by
    unfold L mvOptimalSmoothingLength
    rw [Nat.cast_max]
    apply max_le
    · norm_num
      linarith
    · exact (Nat.ceil_lt_add_one hr0).le
  have hLY : L ≤ Y := hLA.trans hAY
  have hZLK : Z + L ≤ K := (Nat.add_le_add_left hLA Z).trans hZAK
  have hraw := norm_mvIntervalCoefficientSum_le_of_balancedDivisors
    hQ hYZ hYK hwidthLower hL hLY hZLK c hc hS hfull
  have hhalfA : (Z - Y) / 2 ≤ A := (Nat.div_le_self _ _).trans hwidthUpper
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hrsq : r ^ 2 = (A : ℝ) * S := by
    dsimp [r]
    exact Real.sq_sqrt hAS
  have hquot : (A : ℝ) * S / L ≤ r := by
    rw [div_le_iff₀ hLr]
    rw [← hrsq]
    simpa [pow_two] using mul_le_mul_of_nonneg_left hrL hr0
  have hhalfQuot :
      (((Z - Y) / 2 : ℕ) : ℝ) * S / L ≤ r := by
    have hm : ((((Z - Y) / 2 : ℕ) : ℝ)) ≤ (A : ℝ) := by exact_mod_cast hhalfA
    have hmul : ((((Z - Y) / 2 : ℕ) : ℝ)) * S ≤ (A : ℝ) * S :=
      mul_le_mul_of_nonneg_right hm hS
    exact (div_le_div_of_nonneg_right hmul hLr.le).trans hquot
  have hSr : S ≤ r := by
    dsimp [r]
    rw [Real.le_sqrt hS hAS]
    have hSA' : S ≤ (A : ℝ) := by exact_mod_cast hSA
    nlinarith
  dsimp only [r, L] at hraw ⊢
  have hLupper' : ((mvOptimalSmoothingLength A S : ℕ) : ℝ) ≤
      Real.sqrt ((A : ℝ) * S) + 1 := by simpa [r, L] using hLupper
  have hhalfQuot' :
      (((Z - Y) / 2 : ℕ) : ℝ) * S /
          (mvOptimalSmoothingLength A S : ℝ) ≤
        Real.sqrt ((A : ℝ) * S) := by simpa [r, L] using hhalfQuot
  have hSr' : S ≤ Real.sqrt ((A : ℝ) * S) := by simpa [r] using hSr
  calc
    _ ≤ (2 * (((Z - Y) / 2 : ℕ) : ℝ) /
          (mvOptimalSmoothingLength A S : ℝ) + 1) * S +
        (4 * (mvOptimalSmoothingLength A S : ℝ) + 3 * Q + 3) := hraw
    _ ≤ 7 * Real.sqrt ((A : ℝ) * S) + 3 * Q + 7 := by
      have hrewrite :
          (2 * (((Z - Y) / 2 : ℕ) : ℝ) /
              (mvOptimalSmoothingLength A S : ℝ) + 1) * S =
            2 * ((((Z - Y) / 2 : ℕ) : ℝ) * S /
              (mvOptimalSmoothingLength A S : ℝ)) + S := by ring
      rw [hrewrite]
      push_cast
      linarith

/-- A coefficient interval of width at most one contains at most one term. -/
theorem norm_mvIntervalCoefficientSum_le_short
    {K Q Y Z : ℕ} (hQ : 1 ≤ Q) (hYZ : Y ≤ Z) (hwidth : Z - Y < 2)
    (c : Fin K → ℂ)
    (hc : ∀ n : Fin K, ‖c n‖ ≤ mvBalancedDivisorCount Q n.val) :
    ‖mvIntervalCoefficientSum K c Y Z‖ ≤ (Q : ℝ) + 1 := by
  let active : Finset (Fin K) := (Finset.univ : Finset (Fin K)).filter fun n =>
    Y < n.val ∧ n.val ≤ Z
  have hsum : mvIntervalCoefficientSum K c Y Z = ∑ n ∈ active, c n := by
    unfold mvIntervalCoefficientSum
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : Y < n.val ∧ n.val ≤ Z
    · rw [if_pos hn, if_pos (by simpa [active] using hn), mul_one]
    · rw [if_neg hn, if_neg (by simpa [active] using hn), mul_zero]
  have hcard : active.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    apply Fin.ext
    omega
  have hterm : ∀ n ∈ active, ‖c n‖ ≤ (Q : ℝ) + 1 := by
    intro n _
    have hcN := hc n
    have hcount : mvBalancedDivisorCount Q n.val ≤ Q + 1 := by
      unfold mvBalancedDivisorCount
      calc
        _ ≤ (Finset.Icc Q (2 * Q)).card := Finset.card_filter_le _ _
        _ = Q + 1 := by rw [Nat.card_Icc]; omega
    exact hcN.trans (by exact_mod_cast hcount)
  rw [hsum]
  calc
    _ ≤ ∑ n ∈ active, ‖c n‖ := norm_sum_le _ _
    _ ≤ active.card • ((Q : ℝ) + 1) :=
      Finset.sum_le_card_nsmul active (fun n => ‖c n‖) ((Q : ℝ) + 1) hterm
    _ ≤ 1 • ((Q : ℝ) + 1) := by
      gcongr
    _ = (Q : ℝ) + 1 := by simp

/-- MV24.9 including the degenerate endpoint slices arising in MV24.10. -/
theorem norm_mvIntervalCoefficientSum_le_sqrt_all
    {K Q A Y Z : ℕ} (hQ : 1 ≤ Q) (hA : 1 ≤ A)
    (hYZ : Y ≤ Z) (hYK : Y < K)
    (hwidthUpper : Z - Y ≤ A) (hAY : A ≤ Y) (hZAK : Z + A ≤ K)
    (c : Fin K → ℂ)
    (hc : ∀ n : Fin K, ‖c n‖ ≤ mvBalancedDivisorCount Q n.val)
    {S : ℝ} (hS : 0 ≤ S) (hSA : S ≤ A)
    (hfull : ∀ β : ℝ, ‖mvTrigSum K c β‖ ≤ S) :
    ‖mvIntervalCoefficientSum K c Y Z‖ ≤
      7 * Real.sqrt ((A : ℝ) * S) + 3 * Q + 7 := by
  by_cases hwidthLower : 2 ≤ Z - Y
  · exact norm_mvIntervalCoefficientSum_le_sqrt hQ hA hYZ hYK hwidthLower
      hwidthUpper hAY hZAK c hc hS hSA hfull
  · have hshort := norm_mvIntervalCoefficientSum_le_short hQ hYZ (by omega) c hc
    have hsqrt : 0 ≤ Real.sqrt ((A : ℝ) * S) := by positivity
    have hQr : (0 : ℝ) ≤ Q := by positivity
    linarith

end

end RHTower.Sieve
