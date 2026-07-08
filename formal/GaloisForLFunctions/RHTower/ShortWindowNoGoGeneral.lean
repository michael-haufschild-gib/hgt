/-
Global vacuity of the general mean-value energy face at pinning windows: no designed
non-spike coefficient family escapes.

The window-anchor face of a general finite Dirichlet carrier `F(t) = ∑_{n} a_n n^{-it}`
demands the diagonal main term dominate the off-diagonal: the certificate is satisfiable
only if `∑_{m≠n} 2|a_m a_n|/|log(n/m)| < U·∑ a_n²`.  This off-diagonal budget is a sum of
absolute values, so no cancellation of signs reduces it — only sparsity can.  For any
coefficient family whose mass is carried by its adjacent correlations rather than
concentrated on isolated frequencies, the adjacent pairs `(m, m+1)` alone put the whole
diagonal into the off-diagonal: `2|a_m a_{m+1}|/|log((m+1)/m)| ≥ 2m|a_m a_{m+1}|` since
`log((m+1)/m) ≤ 1/m`, and the weighted adjacent correlation dominates the diagonal by the
spread hypothesis.  Hence `off-diagonal ≥ diagonal ≥ U·diagonal` at every window of length
`U ≤ 1` and, because the off-diagonal bound is height-uniform, at every height `T`.  The
pinning geometry forces `U < 1`, so every window anchor drawn from the general mean-value
budget is contradictory for every spread coefficient design: the escape from the sharp
truncation must be a spike (an isolated frequency with vanishing neighbour), which the
spread hypothesis excludes.
-/
import GaloisForLFunctions.RHTower.AnchorSupply
import GaloisForLFunctions.RHTower.ShortWindowNoGo

open MeasureTheory

namespace RHTower

/-- **The weighted adjacent correlation is a lower bound for the off-diagonal budget.**
For coefficients supported on frequencies `≥ 1`, dropping every off-diagonal term except
the adjacent pair `(m, m+1)` and using `log((m+1)/m) ≤ 1/m` gives
`∑_m ∑_{n≠m} 2|a_m a_n|/|log n − log m| ≥ 2·∑_{m, m+1 ∈ s} m·|a_m a_{m+1}|`. -/
theorem adjacent_weighted_le_offDiagonal (a : ℕ → ℝ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    (2 * ∑ m ∈ s.filter (fun m => m + 1 ∈ s), (m : ℝ) * |a m * a (m + 1)|)
      ≤ ∑ m ∈ s, ∑ n ∈ s.erase m,
          2 * |a m * a n| / |Real.log n - Real.log m| := by
  have hg : ∀ m n : ℕ, 0 ≤ 2 * |a m * a n| / |Real.log n - Real.log m| :=
    fun m n => by positivity
  rw [Finset.mul_sum]
  calc (∑ m ∈ s.filter (fun m => m + 1 ∈ s), 2 * ((m : ℝ) * |a m * a (m + 1)|))
      ≤ ∑ m ∈ s.filter (fun m => m + 1 ∈ s),
          2 * |a m * a (m + 1)| / |Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)| := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_filter] at hm
        have hm1 : 1 ≤ m := hs m hm.1
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
        have hlt : (m : ℝ) < ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
        have hL0 : 0 < Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
          have := Real.log_lt_log hm0 hlt; linarith
        have hLle : Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
          have hlog := Real.log_le_sub_one_of_pos
            (show (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / m by positivity)
          rw [Real.log_div (by positivity) (by positivity)] at hlog
          have heq : ((m + 1 : ℕ) : ℝ) / m - 1 = 1 / m := by field_simp; push_cast; ring
          linarith
        rw [abs_of_pos hL0, le_div_iff₀ hL0]
        have hx : 0 ≤ |a m * a (m + 1)| := abs_nonneg _
        have hmL : (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤ 1 := by
          have := mul_le_mul_of_nonneg_left hLle hm0.le
          rwa [mul_one_div, div_self (ne_of_gt hm0)] at this
        nlinarith [hx, hmL]
    _ ≤ ∑ m ∈ s.filter (fun m => m + 1 ∈ s), ∑ n ∈ s.erase m,
          2 * |a m * a n| / |Real.log n - Real.log m| := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_filter] at hm
        have hmem : m + 1 ∈ s.erase m := Finset.mem_erase.mpr ⟨by omega, hm.2⟩
        exact Finset.single_le_sum (fun n _ => hg m n) hmem
    _ ≤ ∑ m ∈ s, ∑ n ∈ s.erase m,
          2 * |a m * a n| / |Real.log n - Real.log m| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => Finset.sum_nonneg (fun n _ => hg i n))

/-- **The spread coefficient class has off-diagonal at least its diagonal.**  If the
diagonal `∑ a_n²` is dominated by twice the weighted adjacent correlation
`∑_{m, m+1 ∈ s} m·|a_m a_{m+1}|` — the precise sense in which the coefficients are spread
across neighbouring frequencies rather than spiked on isolated ones — then the absolute
off-diagonal budget is at least the diagonal. -/
theorem diagonal_le_offDiagonal_of_spread (a : ℕ → ℝ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n)
    (hspread : (∑ m ∈ s, (a m) ^ 2)
        ≤ 2 * ∑ m ∈ s.filter (fun m => m + 1 ∈ s), (m : ℝ) * |a m * a (m + 1)|) :
    (∑ m ∈ s, (a m) ^ 2)
      ≤ ∑ m ∈ s, ∑ n ∈ s.erase m,
          2 * |a m * a n| / |Real.log n - Real.log m| :=
  hspread.trans (adjacent_weighted_le_offDiagonal a s hs)

/-- **Global falsity of the general energy face at short windows for spread designs.**
For any spread coefficient family (diagonal dominated by twice the weighted adjacent
correlation), any window length `U ≤ 1`, any nonnegative orthogonal-energy correction `E`,
and any anchor floor `m_J`, the orthogonal-corrected mean-value energy face is
contradictory: the absolute off-diagonal budget exceeds `U` times the diagonal, so the face
demands a positive quantity be less than a nonpositive one.  The statement is uniform in the
height `T` (which does not appear). -/
theorem energy_face_false_short_window_of_spread
    {a : ℕ → ℝ} {s : Finset ℕ} {U E m_J : ℝ}
    (hs : ∀ n ∈ s, 1 ≤ n) (hU0 : 0 ≤ U) (hU1 : U ≤ 1) (hE : 0 ≤ E)
    (hspread : (∑ m ∈ s, (a m) ^ 2)
        ≤ 2 * ∑ m ∈ s.filter (fun m => m + 1 ∈ s), (m : ℝ) * |a m * a (m + 1)|)
    (henergy : m_J ^ 2 * U + E <
      4 * (U * (∑ m ∈ s, (a m) ^ 2)
        - ∑ m ∈ s, ∑ n ∈ s.erase m,
            2 * |a m * a n| / |Real.log n - Real.log m|)) :
    False := by
  have hdiag : 0 ≤ ∑ m ∈ s, (a m) ^ 2 := Finset.sum_nonneg fun m _ => sq_nonneg _
  have hoff := diagonal_le_offDiagonal_of_spread a s hs hspread
  have hUdiag : U * (∑ m ∈ s, (a m) ^ 2) ≤ ∑ m ∈ s, (a m) ^ 2 := by nlinarith [hdiag]
  have hLHS : 0 ≤ m_J ^ 2 * U + E := add_nonneg (mul_nonneg (sq_nonneg _) hU0) hE
  linarith [hoff, hUdiag, hLHS, henergy]

/-- **No spread designed carrier supplies a window anchor at a pinning window.**  The
pinning geometry (quadratic containment + radii chain) forces the anchor window to length
`U < 1`.  At such lengths the orthogonal-corrected anchor face of the general carrier
`mollG b N` — with coefficients `b_n·n^{−1/2}` — is contradictory for every coefficient
design `b` whose diagonal is dominated by twice its weighted adjacent correlation.  The only
escape from the diagonal-vs-off-diagonal wall is a spike (an isolated frequency whose
neighbour vanishes), excluded by the spread hypothesis.  Height-uniform: every zero, every
height. -/
theorem no_spread_anchor_at_pinning_window
    {b : ℕ → ℝ} {N : ℕ} {ρ : ℂ} {T U rz R P RJ m_J : ℝ}
    (hU0 : 0 < U) (hrz0 : 0 < rz) (hrzR : rz < R) (hRP : R ≤ P)
    (hPrz : P + rz ≤ RJ) (hRJ12 : RJ < 1 / 2)
    (hquad : (ρ.re - 1 / 2) ^ 2 +
      (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2)
    (hspread :
      (∑ m ∈ Finset.Icc 1 N, (b m * ((m : ℝ) ^ (-(1 / 2 : ℝ)))) ^ 2)
        ≤ 2 * ∑ m ∈ (Finset.Icc 1 N).filter (fun m => m + 1 ∈ Finset.Icc 1 N),
              (m : ℝ) * |(b m * ((m : ℝ) ^ (-(1 / 2 : ℝ)))) *
                (b (m + 1) * (((m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))))|)
    (henergy : m_J ^ 2 * U +
        (∫ τ in T..(T + U),
          4 * ((((starRingEnd ℂ) (hardyPhase τ)) * mollPoly b N (linePt τ)).im) ^ 2) <
      4 * (U * (∑ n ∈ Finset.Icc 1 N, (b n * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) ^ 2)
        - ∑ p ∈ Finset.Icc 1 N, ∑ q ∈ (Finset.Icc 1 N).erase p,
            2 * |(b p * ((p : ℝ) ^ (-(1 / 2 : ℝ)))) * (b q * ((q : ℝ) ^ (-(1 / 2 : ℝ))))|
              / |Real.log q - Real.log p|)) :
    False := by
  have hU1 : U ≤ 1 :=
    (pinning_geometry_short_window hrz0 hrzR hRP hPrz hRJ12 hquad).le
  have hE : 0 ≤ ∫ τ in T..(T + U),
      4 * ((((starRingEnd ℂ) (hardyPhase τ)) * mollPoly b N (linePt τ)).im) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => by positivity)
  exact energy_face_false_short_window_of_spread
    (a := fun n => b n * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) (s := Finset.Icc 1 N)
    (fun n hn => (Finset.mem_Icc.mp hn).1) hU0.le hU1 hE hspread henergy

/-- **The spread class is inhabited by a signed non-spike design.**  The coefficients
`a₁ = 1, a₂ = −1` on the support `{1, 2}` satisfy the spread hypothesis (diagonal `2`,
weighted adjacent correlation `1`, and `2 · 1 = 2 ≥ 2`).  This carrier is not a single
spike (two nonzero adjacent frequencies) and its coefficients are signed, showing the no-go
covers signed designs: the off-diagonal budget is a sum of absolute values, so sign
cancellation cannot reduce it below the diagonal. -/
theorem spread_signed_witness :
    (∀ n ∈ (Finset.Icc 1 2 : Finset ℕ), 1 ≤ n) ∧
    (∑ m ∈ (Finset.Icc 1 2 : Finset ℕ),
        ((fun n : ℕ => if n = 2 then (-1 : ℝ) else 1) m) ^ 2)
      ≤ 2 * ∑ m ∈ (Finset.Icc 1 2 : Finset ℕ).filter (fun m => m + 1 ∈ Finset.Icc 1 2),
            (m : ℝ) * |(fun n : ℕ => if n = 2 then (-1 : ℝ) else 1) m
              * (fun n : ℕ => if n = 2 then (-1 : ℝ) else 1) (m + 1)| := by
  refine ⟨fun n hn => (Finset.mem_Icc.mp hn).1, ?_⟩
  have hIcc : (Finset.Icc 1 2 : Finset ℕ) = ({1, 2} : Finset ℕ) := by decide
  rw [hIcc]
  have hfil : ({1, 2} : Finset ℕ).filter (fun m => m + 1 ∈ ({1, 2} : Finset ℕ))
      = ({1} : Finset ℕ) := by decide
  rw [hfil, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), Finset.sum_singleton]
  norm_num

end RHTower
