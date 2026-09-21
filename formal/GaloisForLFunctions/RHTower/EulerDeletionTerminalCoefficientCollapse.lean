import GaloisForLFunctions.RHTower.EulerDeletionNonclockLcmTailBridge

/-!
# EDQ terminal-coefficient collapse

At a live future residual `m`, the complete primitive `m`-period and its selected
terminal `m - 1` prefix have the same coefficient: the missing endpoint is a whole
`m * C` discrepancy span and is exactly zero.  The identical endpoint law holds for
every reciprocal-divisor summand of the cutoff boundary.  Thus the physical EDQ
cofactor fibre has one signed coefficient rather than independent temporal and
spatial coefficients.
-/

noncomputable section
set_option autoImplicit false

open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower.DeletionResidueMartingale

/-- The primitive cofactor prefix returns exactly to zero at its final state in every positive
residual period.  This is componentwise full-span discrepancy cancellation, not a period average
or an asymptotic assertion. -/
theorem cofactorReducedResiduePrefix_pred_eq_zero
    (m t C : ℕ) (hm : 0 < m) (hC : 0 < C) :
    cofactorReducedResiduePrefix m t C (m - 1) = 0 := by
  rw [← cofactor_moebius_discrepancy_prefix_eq_cofactorReducedResiduePrefix
    m t C (m - 1) hm hC]
  apply Finset.sum_eq_zero
  intro r hr
  have hrpos : 0 < r := Nat.pos_of_mem_divisors hr
  have hrC : r ∣ C := Nat.dvd_of_mem_divisors hr
  have hm_eq : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hm)
  have hspan : m * r ∣ (m - 1 + 1) * C := by
    rw [hm_eq]
    exact Nat.mul_dvd_mul_left m hrC
  rw [divisorWindowDiscrepancy_prefix_eq_zero_of_dvd_span
    (m * r) t C (m - 1) (Nat.mul_pos hm hrpos) hC hspan]
  ring

/-- Dropping the zero endpoint does not change a primitive cofactor period polynomial. -/
theorem cofactorReducedResiduePrefix_block_eq_tail
    (m t C : ℕ) (x : ℝ) (hm : 0 < m) (hC : 0 < C) :
    (∑ a ∈ range m, cofactorReducedResiduePrefix m t C a * x ^ (a * C)) =
      ∑ a ∈ range (m - 1), cofactorReducedResiduePrefix m t C a * x ^ (a * C) := by
  have hm_eq : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hm)
  have hlast : cofactorReducedResiduePrefix m t C (m - 1) * x ^ ((m - 1) * C) = 0 := by
    rw [cofactorReducedResiduePrefix_pred_eq_zero m t C hm hC]
    ring
  calc
    _ = ∑ a ∈ range (m - 1 + 1),
        cofactorReducedResiduePrefix m t C a * x ^ (a * C) := by rw [hm_eq]
    _ = (∑ a ∈ range (m - 1),
        cofactorReducedResiduePrefix m t C a * x ^ (a * C)) + 0 := by
          rw [Finset.sum_range_succ, hlast]
    _ = _ := by ring

/-- A live residual divides the ambient quotient, so its selected `Q - 1` block count is exactly
`Q / m`; no terminal quotient correction remains. -/
theorem canonicalClockRatio_sub_one_div_add_one_eq_div
    {N L m : ℕ} (hLN : L ≤ N) (hm : m ∈ futureResidualCarrier N L) :
    (canonicalClockRatio N L - 1) / m + 1 = canonicalClockRatio N L / m := by
  have hmpos : 0 < m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  have hratio : 0 < canonicalClockRatio N L := by
    rw [canonicalClockRatio_eq_div_of_le N L hLN]
    exact Nat.div_pos (Nat.le_of_dvd (clock_pos N) (clock_dvd hLN)) (clock_pos L)
  obtain ⟨k, hk⟩ := mem_futureResidualCarrier_dvd_canonicalClockRatio hLN hm
  have hmk : 0 < m * k := by simpa [hk] using hratio
  have hkpos : 0 < k := Nat.pos_of_ne_zero fun hkzero => by
    subst k
    simp at hmk
  rw [hk, Nat.mul_sub_div 0 m k hmk, Nat.mul_div_right k hmpos]
  simpa using Nat.sub_add_cancel (Nat.succ_le_iff.mpr hkpos)

/-- The complete residual quotient blocks carry a common geometric numerator.  This exact
identity is the arithmetic source of resolvent cancellation away from the beta endpoint; it does
not assert cancellation of the signed residual coefficients. -/
theorem futureResidual_geometric_period_identity
    {N L m : ℕ} (x : ℝ) (hLN : L ≤ N) (hm : m ∈ futureResidualCarrier N L) :
    (1 - x ^ clock L) *
        (∑ q ∈ range (canonicalClockRatio N L / m), x ^ (q * (m * clock L))) *
        (∑ a ∈ range m, x ^ (a * clock L)) =
      1 - x ^ clock N := by
  let Q := canonicalClockRatio N L
  let C := clock L
  let z : ℝ := x ^ C
  have hdiv : m ∣ Q := by
    exact mem_futureResidualCarrier_dvd_canonicalClockRatio hLN hm
  have hQM : m * (Q / m) = Q := Nat.mul_div_cancel' hdiv
  have hQC : Q * C = clock N := by
    dsimp [Q, C]
    rw [canonicalClockRatio_eq_div_of_le N L hLN]
    exact Nat.div_mul_cancel (clock_dvd hLN)
  have hpowC (n : ℕ) : x ^ (n * C) = z ^ n := by
    dsimp [z]
    simpa [Nat.mul_comm] using (pow_mul x C n)
  have hpowBlock (n : ℕ) : x ^ (n * (m * C)) = (z ^ m) ^ n := by
    rw [show n * (m * C) = (m * n) * C by ring, hpowC]
    dsimp [z]
    rw [pow_mul]
  have hgeomSmall : (1 - z) * ∑ a ∈ range m, z ^ a = 1 - z ^ m := by
    calc
      (1 - z) * ∑ a ∈ range m, z ^ a = -((z - 1) * ∑ a ∈ range m, z ^ a) := by ring
      _ = -(z ^ m - 1) := by rw [mul_geom_sum]
      _ = 1 - z ^ m := by ring
  have hgeomBig : (1 - z ^ m) * ∑ q ∈ range (Q / m), (z ^ m) ^ q =
      1 - (z ^ m) ^ (Q / m) := by
    calc
      (1 - z ^ m) * ∑ q ∈ range (Q / m), (z ^ m) ^ q =
          -((z ^ m - 1) * ∑ q ∈ range (Q / m), (z ^ m) ^ q) := by ring
      _ = -((z ^ m) ^ (Q / m) - 1) := by rw [mul_geom_sum]
      _ = 1 - (z ^ m) ^ (Q / m) := by ring
  have hmain : (1 - z) *
      (∑ q ∈ range (Q / m), (z ^ m) ^ q) *
      (∑ a ∈ range m, z ^ a) = 1 - z ^ Q := by
    calc
      (1 - z) * (∑ q ∈ range (Q / m), (z ^ m) ^ q) *
          ∑ a ∈ range m, z ^ a =
          ((1 - z) * ∑ a ∈ range m, z ^ a) * ∑ q ∈ range (Q / m), (z ^ m) ^ q := by ring
      _ = (1 - z ^ m) * ∑ q ∈ range (Q / m), (z ^ m) ^ q := by rw [hgeomSmall]
      _ = 1 - (z ^ m) ^ (Q / m) := hgeomBig
      _ = 1 - z ^ Q := by rw [← pow_mul, hQM]
  calc
    (1 - x ^ clock L) *
        (∑ q ∈ range (canonicalClockRatio N L / m), x ^ (q * (m * clock L))) *
        (∑ a ∈ range m, x ^ (a * clock L)) =
        (1 - z) * (∑ q ∈ range (Q / m), (z ^ m) ^ q) *
          ∑ a ∈ range m, z ^ a := by
            dsimp [Q, C] at hpowC hpowBlock ⊢
            simp_rw [hpowC, hpowBlock]
            rfl
    _ = 1 - z ^ Q := hmain
    _ = 1 - x ^ clock N := by
      dsimp [z]
      rw [← hpowC, hQC]

/-- A complete residual geometric factor may be moved to the common ambient numerator.  The
coefficient function is arbitrary: this is a finite exact factorization, not a cancellation or
bound for the signed coefficients. -/
theorem futureResidual_geometric_factorization
    (N L : ℕ) (A : ℕ → ℝ) (x : ℝ) (hLN : L ≤ N) (hx : 0 ≤ x) :
    (1 - x ^ clock L) *
        (∑ m ∈ futureResidualCarrier N L,
          A m * ∑ q ∈ range (canonicalClockRatio N L / m),
            x ^ (q * (m * clock L))) =
      (1 - x ^ clock N) *
        ∑ m ∈ futureResidualCarrier N L,
          A m / (∑ a ∈ range m, x ^ (a * clock L)) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmpos : 0 < m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  have hgeom := futureResidual_geometric_period_identity x hLN hm
  have hdenom : (∑ a ∈ range m, x ^ (a * clock L)) ≠ 0 := by
    have hpos : 0 < ∑ a ∈ range m, (x ^ clock L) ^ a :=
      geom_sum_pos (pow_nonneg hx _) hmpos.ne'
    have hpow (a : ℕ) : x ^ (a * clock L) = (x ^ clock L) ^ a := by
      simpa [Nat.mul_comm] using (pow_mul x (clock L) a)
    simpa only [hpow] using hpos.ne'
  have hscalar :
      (1 - x ^ clock L) *
          (∑ q ∈ range (canonicalClockRatio N L / m), x ^ (q * (m * clock L))) =
        (1 - x ^ clock N) / (∑ a ∈ range m, x ^ (a * clock L)) := by
    apply (eq_div_iff hdenom).mpr
    calc
      ((1 - x ^ clock L) *
          ∑ q ∈ range (canonicalClockRatio N L / m), x ^ (q * (m * clock L))) *
          ∑ a ∈ range m, x ^ (a * clock L) =
          (1 - x ^ clock L) *
            (∑ q ∈ range (canonicalClockRatio N L / m), x ^ (q * (m * clock L))) *
            (∑ a ∈ range m, x ^ (a * clock L)) := by ring
      _ = _ := hgeom
  rw [div_eq_mul_inv]
  calc
    (1 - x ^ clock L) *
        (A m * ∑ q ∈ range (canonicalClockRatio N L / m), x ^ (q * (m * clock L))) =
        A m * ((1 - x ^ clock L) *
          ∑ q ∈ range (canonicalClockRatio N L / m), x ^ (q * (m * clock L))) := by ring
    _ = A m * ((1 - x ^ clock N) *
        (∑ a ∈ range m, x ^ (a * clock L))⁻¹) := by rw [hscalar, div_eq_mul_inv]
    _ = (1 - x ^ clock N) * (A m * (∑ a ∈ range m, x ^ (a * clock L))⁻¹) := by ring

/-- The literal cutoff boundary has the same zero endpoint as its complete primitive partner.
Consequently its complete-period and terminal coefficients coincide identically. -/
theorem complementBoundaryBlock_eq_tail
    (N L m t : ℕ) (x : ℝ) (hm : 0 < m) :
    complementBoundaryBlock N L m t x = complementBoundaryTail N L m t x := by
  unfold complementBoundaryBlock complementBoundaryTail
  refine Finset.sum_congr rfl fun q hq => ?_
  by_cases hsq : Squarefree (m * (clock L / q))
  · simp only [if_pos hsq]
    have hqpos : 0 < q := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hq).1
    have hm_eq : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hm)
    have hlast :
        (∑ i ∈ range (m - 1 + 1),
          divisorWindowDiscrepancy m (t / (clock L / q) + i * q) q) *
            x ^ ((m - 1) * clock L) = 0 := by
      rw [divisorWindowDiscrepancy_prefix_eq_zero_of_dvd_span m
        (t / (clock L / q)) q (m - 1) hm hqpos]
      · ring
      · rw [hm_eq]
        exact dvd_mul_right m q
    have hsum :
        (∑ a ∈ range m,
          (∑ i ∈ range (a + 1),
            divisorWindowDiscrepancy m (t / (clock L / q) + i * q) q) *
              x ^ (a * clock L)) =
          ∑ a ∈ range (m - 1),
            (∑ i ∈ range (a + 1),
              divisorWindowDiscrepancy m (t / (clock L / q) + i * q) q) *
                x ^ (a * clock L) := by
      calc
        _ = ∑ a ∈ range (m - 1 + 1),
            (∑ i ∈ range (a + 1),
              divisorWindowDiscrepancy m (t / (clock L / q) + i * q) q) *
                x ^ (a * clock L) := by rw [hm_eq]
        _ = (∑ a ∈ range (m - 1),
            (∑ i ∈ range (a + 1),
              divisorWindowDiscrepancy m (t / (clock L / q) + i * q) q) *
                x ^ (a * clock L)) + 0 := by
              rw [Finset.sum_range_succ, hlast]
        _ = _ := by ring
    exact congrArg (fun z : ℝ => ((moebius (clock L / q) : ℤ) : ℝ) * z) hsum
  · simp [hsq]

/-- The complete block and terminal tail share one signed coefficient before their adjacent
geometric factors are joined. -/
theorem futureOldCofactorCarrier_sum_eq_single_terminal_coefficient
    {N L m : ℕ} (t : ℕ) (x : ℝ) (hLN : L ≤ N)
    (hm : m ∈ futureResidualCarrier N L) :
    (∑ r ∈ futureOldCofactorCarrier N L m,
      clockResidualBetaWeight L t (canonicalClockRatio N L - 1) x (m * r)) =
      ((moebius m : ℤ) : ℝ) *
        ((∑ a ∈ range (m - 1),
          cofactorReducedResiduePrefix m t (clock L) a * x ^ (a * clock L) -
          complementBoundaryTail N L m t x) *
          ((∑ b ∈ range ((canonicalClockRatio N L - 1) / m),
            x ^ (b * (m * clock L))) +
            x ^ (((canonicalClockRatio N L - 1) / m) * (m * clock L)))) := by
  have hmpos : 0 < m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  rw [futureOldCofactorCarrier_sum_eq_factorized_terminal_coefficients t x hLN hm,
    cofactorReducedResiduePrefix_block_eq_tail m t (clock L) x hmpos (clock_pos L),
    complementBoundaryBlock_eq_tail N L m t x hmpos]
  ring

/-- Each selected physical EDQ residual fibre has one exact signed period coefficient.  The
former complete-block versus terminal-tail mismatch is absent; only the signed cross-residual
sum of these explicit coefficients remains to be controlled. -/
theorem futureOldCofactorCarrier_sum_eq_single_period_coefficient
    {N L m : ℕ} (t : ℕ) (x : ℝ) (hLN : L ≤ N)
    (hm : m ∈ futureResidualCarrier N L) :
    (∑ r ∈ futureOldCofactorCarrier N L m,
      clockResidualBetaWeight L t (canonicalClockRatio N L - 1) x (m * r)) =
      ((moebius m : ℤ) : ℝ) *
        ((∑ a ∈ range (m - 1),
          cofactorReducedResiduePrefix m t (clock L) a * x ^ (a * clock L) -
          complementBoundaryTail N L m t x) *
          ∑ b ∈ range ((canonicalClockRatio N L - 1) / m + 1),
            x ^ (b * (m * clock L))) := by
  rw [futureOldCofactorCarrier_sum_eq_single_terminal_coefficient t x hLN hm,
    ← Finset.sum_range_succ]

/-- The literal selected truncated-divisor block has the collapsed one-coefficient residual
normal form.  This inserts the terminal-coefficient collapse into the physical source kernel
itself; no cofactor surrogate or averaged period is introduced. -/
theorem truncatedDivisorBlockKernel_eq_source_single_period_cofactors
    (N l u b : ℕ) (x : ℝ) (hlN : l < N) :
    truncatedDivisorBlockKernel N l u b x =
      (x ^ (u + b * clock l) *
        ((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
          x ^ clock (l + 1) * (1 - x ^ clock (l + 1)) *
            ∑ m ∈ futureResidualCarrier N (l + 1),
              ((moebius m : ℤ) : ℝ) *
                ((∑ a ∈ range (m - 1),
                  cofactorReducedResiduePrefix m (u + b * clock l + 1) (clock (l + 1)) a *
                    x ^ (a * clock (l + 1)) -
                  complementBoundaryTail N (l + 1) m (u + b * clock l + 1) x) *
                  ∑ q ∈ range ((canonicalClockRatio N (l + 1) - 1) / m + 1),
                    x ^ (q * (m * clock (l + 1))))) *
        (1 - x ^ clock N)⁻¹) /
      (∑ a ∈ range (clock (l + 1)), x ^ a) := by
  have hsum :
      (∑ m ∈ futureResidualCarrier N (l + 1),
        ∑ r ∈ futureOldCofactorCarrier N (l + 1) m,
          clockResidualBetaWeight (l + 1) (u + b * clock l + 1)
            (canonicalClockRatio N (l + 1) - 1) x (m * r)) =
        ∑ m ∈ futureResidualCarrier N (l + 1),
          ((moebius m : ℤ) : ℝ) *
            ((∑ a ∈ range (m - 1),
              cofactorReducedResiduePrefix m (u + b * clock l + 1) (clock (l + 1)) a *
                x ^ (a * clock (l + 1)) -
              complementBoundaryTail N (l + 1) m (u + b * clock l + 1) x) *
              ∑ q ∈ range ((canonicalClockRatio N (l + 1) - 1) / m + 1),
                x ^ (q * (m * clock (l + 1)))) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact futureOldCofactorCarrier_sum_eq_single_period_coefficient
      (u + b * clock l + 1) x (Nat.succ_le_iff.mpr hlN) hm
  rw [truncatedDivisorBlockKernel_eq_source_futureCofactor N l u b x hlN, hsum]

/-- Away from the single beta endpoint `x = 1`, the physical EDQ resolvent cancels exactly
against every complete residual geometric block.  The literal selected block is therefore its
paired Möbius source plus one normalized signed residual-cofactor sum, divided only by its
physical child-fibre geometric mass.  No bound or sign claim is made for that remaining sum. -/
theorem truncatedDivisorBlockKernel_eq_source_normalizedResidual
    (N l u b : ℕ) (x : ℝ) (hlN : l < N) (hx : 0 ≤ x) (hx1 : x < 1) :
    truncatedDivisorBlockKernel N l u b x =
      x ^ (u + b * clock l) *
        (pairedMoebiusSource N (u + b * clock l) +
          x ^ clock (l + 1) *
            ∑ m ∈ futureResidualCarrier N (l + 1),
              ((moebius m : ℤ) : ℝ) *
                ((∑ a ∈ range (m - 1),
                  cofactorReducedResiduePrefix m (u + b * clock l + 1) (clock (l + 1)) a *
                    x ^ (a * clock (l + 1)) -
                  complementBoundaryTail N (l + 1) m (u + b * clock l + 1) x) /
                  (∑ a ∈ range m, x ^ (a * clock (l + 1))))) /
        (∑ a ∈ range (clock (l + 1)), x ^ a) := by
  let A : ℕ → ℝ := fun m =>
    ((moebius m : ℤ) : ℝ) *
      (∑ a ∈ range (m - 1),
        cofactorReducedResiduePrefix m (u + b * clock l + 1) (clock (l + 1)) a *
          x ^ (a * clock (l + 1)) -
        complementBoundaryTail N (l + 1) m (u + b * clock l + 1) x)
  let S : ℝ := ∑ m ∈ futureResidualCarrier N (l + 1),
    A m * ∑ q ∈ range (canonicalClockRatio N (l + 1) / m),
      x ^ (q * (m * clock (l + 1)))
  let T : ℝ := ∑ m ∈ futureResidualCarrier N (l + 1),
    A m / ∑ a ∈ range m, x ^ (a * clock (l + 1))
  have hLN : l + 1 ≤ N := Nat.succ_le_iff.mpr hlN
  have hsumPeriod :
      (∑ m ∈ futureResidualCarrier N (l + 1),
        ((moebius m : ℤ) : ℝ) *
          ((∑ a ∈ range (m - 1),
            cofactorReducedResiduePrefix m (u + b * clock l + 1) (clock (l + 1)) a *
              x ^ (a * clock (l + 1)) -
            complementBoundaryTail N (l + 1) m (u + b * clock l + 1) x) *
            ∑ q ∈ range ((canonicalClockRatio N (l + 1) - 1) / m + 1),
              x ^ (q * (m * clock (l + 1))))) = S := by
    rw [show S = ∑ m ∈ futureResidualCarrier N (l + 1),
        A m * ∑ q ∈ range (canonicalClockRatio N (l + 1) / m),
          x ^ (q * (m * clock (l + 1))) by rfl]
    apply Finset.sum_congr rfl
    intro m hm
    rw [canonicalClockRatio_sub_one_div_add_one_eq_div hLN hm]
    dsimp [A]
    ring
  have hres : (1 - x ^ clock (l + 1)) * S = (1 - x ^ clock N) * T := by
    simpa only [S, T] using futureResidual_geometric_factorization N (l + 1) A x hLN hx
  have hnumpos : 0 < 1 - x ^ clock N :=
    sub_pos.mpr (pow_lt_one₀ hx hx1 (clock_pos N).ne')
  have hnum : 1 - x ^ clock N ≠ 0 := ne_of_gt hnumpos
  have hinside :
      (((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
        x ^ clock (l + 1) * ((1 - x ^ clock (l + 1)) * S)) *
        (1 - x ^ clock N)⁻¹) =
        pairedMoebiusSource N (u + b * clock l) + x ^ clock (l + 1) * T := by
    calc
      (((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
        x ^ clock (l + 1) * ((1 - x ^ clock (l + 1)) * S)) *
        (1 - x ^ clock N)⁻¹) =
        ((1 - x ^ clock N) *
          (pairedMoebiusSource N (u + b * clock l) + x ^ clock (l + 1) * T)) *
          (1 - x ^ clock N)⁻¹ := by rw [hres]; ring
      _ = _ := by field_simp
  rw [truncatedDivisorBlockKernel_eq_source_single_period_cofactors N l u b x hlN,
    hsumPeriod]
  have hT :
      (∑ m ∈ futureResidualCarrier N (l + 1),
        ((moebius m : ℤ) : ℝ) *
          ((∑ a ∈ range (m - 1),
            cofactorReducedResiduePrefix m (u + b * clock l + 1) (clock (l + 1)) a *
              x ^ (a * clock (l + 1)) -
            complementBoundaryTail N (l + 1) m (u + b * clock l + 1) x) /
            ∑ a ∈ range m, x ^ (a * clock (l + 1)))) = T := by
    rw [show T = ∑ m ∈ futureResidualCarrier N (l + 1),
        A m / ∑ a ∈ range m, x ^ (a * clock (l + 1)) by rfl]
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [A]
    ring
  rw [hT]
  change x ^ (u + b * clock l) *
      ((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
        x ^ clock (l + 1) * (1 - x ^ clock (l + 1)) * S) *
      (1 - x ^ clock N)⁻¹ /
      (∑ a ∈ range (clock (l + 1)), x ^ a) =
    x ^ (u + b * clock l) *
      (pairedMoebiusSource N (u + b * clock l) + x ^ clock (l + 1) * T) /
      (∑ a ∈ range (clock (l + 1)), x ^ a)
  calc
    x ^ (u + b * clock l) *
        ((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
          x ^ clock (l + 1) * (1 - x ^ clock (l + 1)) * S) *
        (1 - x ^ clock N)⁻¹ /
        (∑ a ∈ range (clock (l + 1)), x ^ a) =
        x ^ (u + b * clock l) *
          (((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
            x ^ clock (l + 1) * ((1 - x ^ clock (l + 1)) * S)) *
            (1 - x ^ clock N)⁻¹) /
          (∑ a ∈ range (clock (l + 1)), x ^ a) := by ring
    _ = _ := by rw [hinside]

end RHTower.DeletionResidueMartingale
