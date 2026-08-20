/-
# Additivity of approximation numbers and the Schatten quasi-triangle

Approximating two operators separately and adding the approximants approximates the sum, so the
approximation numbers are subadditive with additive indices: `a_{i+j}(X+Y) ≤ a_i(X) + a_j(Y)`.
Reading this along the even indices and comparing the odd ones downwards bounds the whole `p`-energy
of a sum by the energies of its summands, with a constant depending only on `p`.  In particular the
Schatten classes are closed under addition and a sum of two Schatten-null sequences is Schatten
null, for every positive exponent -- no triangle inequality for the Schatten norm is needed.

Main results:
* `HasRankLE.add` — ranks add.
* `approxNumber_add_le` — **subadditivity of the approximation numbers**.
* `memSchattenClass_add` — the Schatten classes are additive.
* `schattenNorm_add_rpow_le` — **the quasi-triangle inequality for the `p`-energy**.
* `tendsto_schattenNorm_add` — a sum of two Schatten-null sequences is Schatten null.
-/
import GaloisForLFunctions.HTGeometry.OperatorDeterminantGraphClosure

open Filter Topology ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Ranks add. -/
theorem HasRankLE.add {F G : H →L[ℂ] H} {i j : ℕ} (hF : HasRankLE F i) (hG : HasRankLE G j) :
    HasRankLE (F + G) (i + j) := by
  obtain ⟨V, hV, hVle, hVmem⟩ := hF
  obtain ⟨W, hW, hWle, hWmem⟩ := hG
  haveI := hV
  haveI := hW
  refine ⟨V ⊔ W, Submodule.finiteDimensional_sup V W, ?_, ?_⟩
  · exact (Submodule.finrank_add_le_finrank_add_finrank V W).trans (Nat.add_le_add hVle hWle)
  · intro x
    rw [add_apply]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hVmem x))
      (Submodule.mem_sup_right (hWmem x))

/-- **Subadditivity of the approximation numbers**: approximating the summands separately
approximates the sum with the ranks added. -/
theorem approxNumber_add_le (X Y : H →L[ℂ] H) (i j : ℕ) :
    approxNumber (X + Y) (i + j) ≤ approxNumber X i + approxNumber Y j := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨F, hF, hFlt⟩ := exists_hasRankLE_norm_sub_lt X i
    (show approxNumber X i < approxNumber X i + ε / 2 by linarith)
  obtain ⟨G, hG, hGlt⟩ := exists_hasRankLE_norm_sub_lt Y j
    (show approxNumber Y j < approxNumber Y j + ε / 2 by linarith)
  have hsplit : (X + Y) - (F + G) = (X - F) + (Y - G) := by abel
  calc approxNumber (X + Y) (i + j) ≤ ‖(X + Y) - (F + G)‖ :=
        approxNumber_le _ _ _ (hF.add hG)
    _ ≤ ‖X - F‖ + ‖Y - G‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ approxNumber X i + approxNumber Y j + ε := by linarith

theorem approxNumber_two_mul_add_le (X Y : H →L[ℂ] H) (k : ℕ) :
    approxNumber (X + Y) (2 * k) ≤ approxNumber X k + approxNumber Y k := by
  have h := approxNumber_add_le X Y k k
  rwa [show k + k = 2 * k by ring] at h

/-- The elementary quasi-triangle inequality for real powers. -/
theorem rpow_add_le_two_rpow_mul {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := by
  have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) p
  rcases le_total a b with h | h
  · have hab : a + b ≤ 2 * b := by linarith
    have hstep : (a + b) ^ p ≤ (2 * b) ^ p :=
      Real.rpow_le_rpow (by linarith) hab hp
    have heq : ((2 : ℝ) * b) ^ p = 2 ^ p * b ^ p := Real.mul_rpow (by norm_num) hb
    have hap : (0 : ℝ) ≤ a ^ p := Real.rpow_nonneg ha p
    have hbp : (0 : ℝ) ≤ b ^ p := Real.rpow_nonneg hb p
    calc (a + b) ^ p ≤ 2 ^ p * b ^ p := by rw [← heq]; exact hstep
      _ ≤ 2 ^ p * (a ^ p + b ^ p) := by nlinarith
  · have hab : a + b ≤ 2 * a := by linarith
    have hstep : (a + b) ^ p ≤ (2 * a) ^ p :=
      Real.rpow_le_rpow (by linarith) hab hp
    have heq : ((2 : ℝ) * a) ^ p = 2 ^ p * a ^ p := Real.mul_rpow (by norm_num) ha
    have hap : (0 : ℝ) ≤ a ^ p := Real.rpow_nonneg ha p
    have hbp : (0 : ℝ) ≤ b ^ p := Real.rpow_nonneg hb p
    calc (a + b) ^ p ≤ 2 ^ p * a ^ p := by rw [← heq]; exact hstep
      _ ≤ 2 ^ p * (a ^ p + b ^ p) := by nlinarith

section Additivity

variable {p : ℝ} {X Y : H →L[ℂ] H}

/-- The dominating energy sequence of a sum. -/
private theorem approxNumber_even_rpow_le (hp : 0 < p) (X Y : H →L[ℂ] H) (k : ℕ) :
    approxNumber (X + Y) (2 * k) ^ p
      ≤ 2 ^ p * (approxNumber X k ^ p + approxNumber Y k ^ p) := by
  refine le_trans (Real.rpow_le_rpow (approxNumber_nonneg _ _)
    (approxNumber_two_mul_add_le X Y k) hp.le) ?_
  exact rpow_add_le_two_rpow_mul (approxNumber_nonneg _ _) (approxNumber_nonneg _ _) hp.le

private theorem approxNumber_odd_rpow_le (hp : 0 < p) (X Y : H →L[ℂ] H) (k : ℕ) :
    approxNumber (X + Y) (2 * k + 1) ^ p
      ≤ 2 ^ p * (approxNumber X k ^ p + approxNumber Y k ^ p) := by
  refine le_trans (Real.rpow_le_rpow (approxNumber_nonneg _ _)
    (approxNumber_antitone (X + Y) (Nat.le_succ _)) hp.le) ?_
  exact approxNumber_even_rpow_le hp X Y k

private theorem summable_dominant (hX : MemSchattenClass p X)
    (hY : MemSchattenClass p Y) :
    Summable fun k => 2 ^ p * (approxNumber X k ^ p + approxNumber Y k ^ p) :=
  (hX.add hY).mul_left _

/-- **The Schatten classes are additive.** -/
theorem memSchattenClass_add (hp : 0 < p) (hX : MemSchattenClass p X)
    (hY : MemSchattenClass p Y) : MemSchattenClass p (X + Y) := by
  have hdom := summable_dominant hX hY
  have hev : Summable fun k => approxNumber (X + Y) (2 * k) ^ p :=
    hdom.of_nonneg_of_le (fun k => Real.rpow_nonneg (approxNumber_nonneg _ _) p)
      (approxNumber_even_rpow_le hp X Y)
  have hod : Summable fun k => approxNumber (X + Y) (2 * k + 1) ^ p :=
    hdom.of_nonneg_of_le (fun k => Real.rpow_nonneg (approxNumber_nonneg _ _) p)
      (approxNumber_odd_rpow_le hp X Y)
  exact Summable.even_add_odd (f := fun j => approxNumber (X + Y) j ^ p) hev hod

set_option maxHeartbeats 1000000 in
/-- **The quasi-triangle inequality for the `p`-energy of the approximation numbers.** -/
theorem tsum_rpow_approxNumber_add_le (hp : 0 < p) (hX : MemSchattenClass p X)
    (hY : MemSchattenClass p Y) :
    (∑' j, approxNumber (X + Y) j ^ p)
      ≤ 2 ^ (p + 1) * ((∑' j, approxNumber X j ^ p) + ∑' j, approxNumber Y j ^ p) := by
  have hdom := summable_dominant hX hY
  have hev : Summable fun k => approxNumber (X + Y) (2 * k) ^ p :=
    hdom.of_nonneg_of_le (fun k => Real.rpow_nonneg (approxNumber_nonneg _ _) p)
      (approxNumber_even_rpow_le hp X Y)
  have hod : Summable fun k => approxNumber (X + Y) (2 * k + 1) ^ p :=
    hdom.of_nonneg_of_le (fun k => Real.rpow_nonneg (approxNumber_nonneg _ _) p)
      (approxNumber_odd_rpow_le hp X Y)
  have hsplit := tsum_even_add_odd (f := fun j => approxNumber (X + Y) j ^ p) hev hod
  have hdomval : (∑' k, 2 ^ p * (approxNumber X k ^ p + approxNumber Y k ^ p))
      = 2 ^ p * ((∑' j, approxNumber X j ^ p) + ∑' j, approxNumber Y j ^ p) := by
    rw [tsum_mul_left, hX.tsum_add hY]
  have hevle : (∑' k, approxNumber (X + Y) (2 * k) ^ p)
      ≤ 2 ^ p * ((∑' j, approxNumber X j ^ p) + ∑' j, approxNumber Y j ^ p) := by
    rw [← hdomval]
    exact hev.tsum_le_tsum (approxNumber_even_rpow_le hp X Y) hdom
  have hodle : (∑' k, approxNumber (X + Y) (2 * k + 1) ^ p)
      ≤ 2 ^ p * ((∑' j, approxNumber X j ^ p) + ∑' j, approxNumber Y j ^ p) := by
    rw [← hdomval]
    exact hod.tsum_le_tsum (approxNumber_odd_rpow_le hp X Y) hdom
  have hrw : (2 : ℝ) ^ (p + 1) = 2 * 2 ^ p := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
    ring
  rw [← hsplit, hrw]
  linarith

/-- **The quasi-triangle inequality for the Schatten `p`-energy.** -/
theorem schattenNorm_add_rpow_le (hp : 0 < p) (hX : MemSchattenClass p X)
    (hY : MemSchattenClass p Y) :
    schattenNorm p (X + Y) ^ p
      ≤ 2 ^ (p + 1) * (schattenNorm p X ^ p + schattenNorm p Y ^ p) := by
  rw [schattenNorm_rpow_eq_tsum hp, schattenNorm_rpow_eq_tsum hp, schattenNorm_rpow_eq_tsum hp]
  exact tsum_rpow_approxNumber_add_le hp hX hY

end Additivity

/-- **A sum of two Schatten-null sequences is Schatten null.** -/
theorem tendsto_schattenNorm_add {p : ℝ} (hp : 0 < p) {X Y : ℕ → H →L[ℂ] H}
    (hX : ∀ n, MemSchattenClass p (X n)) (hY : ∀ n, MemSchattenClass p (Y n))
    (hXt : Tendsto (fun n => schattenNorm p (X n)) atTop (nhds 0))
    (hYt : Tendsto (fun n => schattenNorm p (Y n)) atTop (nhds 0)) :
    Tendsto (fun n => schattenNorm p (X n + Y n)) atTop (nhds 0) := by
  have hcontp : ContinuousAt (fun x : ℝ => x ^ p) 0 :=
    Real.continuousAt_rpow_const 0 p (Or.inr hp.le)
  have hzeroP : (0 : ℝ) ^ p = 0 := Real.zero_rpow hp.ne'
  have hXp : Tendsto (fun n => schattenNorm p (X n) ^ p) atTop (nhds 0) := by
    have := hcontp.tendsto.comp hXt
    rwa [hzeroP] at this
  have hYp : Tendsto (fun n => schattenNorm p (Y n) ^ p) atTop (nhds 0) := by
    have := hcontp.tendsto.comp hYt
    rwa [hzeroP] at this
  have hsum : Tendsto
      (fun n => 2 ^ (p + 1) * (schattenNorm p (X n) ^ p + schattenNorm p (Y n) ^ p))
      atTop (nhds 0) := by
    have := (hXp.add hYp).const_mul ((2 : ℝ) ^ (p + 1))
    rwa [add_zero, mul_zero] at this
  have hcontinv : ContinuousAt (fun x : ℝ => x ^ (1 / p)) 0 :=
    Real.continuousAt_rpow_const 0 (1 / p) (Or.inr (by positivity))
  have hfinal := hcontinv.tendsto.comp hsum
  rw [Real.zero_rpow (by positivity : (1 : ℝ) / p ≠ 0)] at hfinal
  refine squeeze_zero (fun n => schattenNorm_nonneg _ _) (fun n => ?_) hfinal
  have hle := schattenNorm_add_rpow_le hp (hX n) (hY n)
  have hnn : (0 : ℝ) ≤ schattenNorm p (X n + Y n) := schattenNorm_nonneg _ _
  calc schattenNorm p (X n + Y n)
      = (schattenNorm p (X n + Y n) ^ p) ^ (1 / p) := by
        rw [← Real.rpow_mul hnn, mul_one_div, div_self hp.ne', Real.rpow_one]
    _ ≤ (2 ^ (p + 1) * (schattenNorm p (X n) ^ p + schattenNorm p (Y n) ^ p)) ^ (1 / p) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hnn p) hle (by positivity)

end

end GaloisForLFunctions.HTGeometry
