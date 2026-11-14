import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.TwoBranchSubintervalBound

/-!
# The fiberwise floor of the folded potential and prime contacts

The folded part of Weil's form at `A = log 2`,
`∫₀¹ G² (c₀ + vTrue) + 2 e₂ ∫₀^{1/2} G(u) G(1-u) + 2 e₃ ∫₀^{L₄} G(1-s) G(a+s)`, `L₄ = (1-a)/2`,
dominates `2 mᵀΛm - mᵀ Qtot m - ∑ pertTot_k m_k²` (`FiberCert.bound`), where the certificate
`FiberCert` consists of contiguous four-branch subintervals of `[0, lo]`, two-branch
subintervals of `[hi, 1/2]` and the two endpoint slivers `(lo, L₄)`, `(1 - a, hi)`.
-/

open Real MeasureTheory Set Finset intervalIntegral
open scoped BigOperators

namespace GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo

open SelectivePositivityAndThresholdLaws

/-! ### Sums of rational matrices -/

/-- Entrywise sum of a list of `K × K` matrices. -/
def sumMat (K : ℕ) (Ms : List (List (List ℚ))) : List (List ℚ) :=
  tabQ K fun i j => (Ms.map fun M => matQ M i j).sum

theorem quadR_sumMat (K : ℕ) (Ms : List (List (List ℚ))) (m : Fin K → ℝ) :
    quadR K (sumMat K Ms) m = (Ms.map fun M => quadR K M m).sum := by
  induction Ms with
  | nil => simp [quadR, sumMat, matQ_tabQ _ (Fin.is_lt _) (Fin.is_lt _)]
  | cons M Ms ih =>
    have h : quadR K (sumMat K (M :: Ms)) m = quadR K M m + quadR K (sumMat K Ms) m := by
      simp only [quadR, sumMat, matQ_tabQ _ (Fin.is_lt _) (Fin.is_lt _), List.map_cons,
        List.sum_cons, Rat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [h, ih, List.map_cons, List.sum_cons]

/-! ### Endpoint slivers -/

/-- The sliver `(lo, (1 - a)/2)` of the four-branch region. -/
structure Sliver4 where
  lo : ℚ
  tay : List TaylorBranch

/-- The sliver `(1 - a, hi)` of the two-branch region. -/
structure Sliver2 where
  hi : ℚ
  tay : List TaylorBranch

namespace Sliver4

variable (S : SectorData) (T : Sliver4)

def tayB (b : ℕ) : TaylorBranch := T.tay.getD b ⟨0, 0, 0, 1, 0⟩

/-- Lower points of the four branches over the sliver. -/
def xl : ℕ → ℚ
  | 0 => T.lo
  | 1 => 1 - (1 - aLoQ) / 2
  | 2 => aLoQ + T.lo
  | _ => 1 - aHiQ - (1 - aLoQ) / 2

def width : ℚ := (1 - aLoQ) / 2 - T.lo

def check : Bool :=
  decide (0 ≤ T.lo) && decide (T.lo ≤ (1 - aHiQ) / 2) &&
    (List.range 4).all (fun b => (T.tayB b).valid && decide (0 < (T.tayB b).om) &&
      decide (0 ≤ T.xl b) && decide ((T.tayB b).t0 ≤ T.xl b ^ 2)) &&
    pivots4Pos (S.c0 + (T.tayB 0).base) (S.c0 + (T.tayB 1).base) (S.c0 + (T.tayB 2).base)
      (S.c0 + (T.tayB 3).base) S.e2 S.e3

def pert (k : ℕ) : ℚ := 4 * T.width * S.K * S.sup k ^ 2

end Sliver4

namespace Sliver2

variable (S : SectorData) (T : Sliver2)

def tayB (b : ℕ) : TaylorBranch := T.tay.getD b ⟨0, 0, 0, 1, 0⟩

def xl : ℕ → ℚ
  | 0 => 1 - aHiQ
  | _ => 1 - T.hi

def width : ℚ := T.hi - (1 - aHiQ)

def check : Bool :=
  decide (1 - aLoQ ≤ T.hi) && decide (T.hi ≤ 1 / 2) &&
    (List.range 2).all (fun b => (T.tayB b).valid && decide (0 < (T.tayB b).om) &&
      decide (0 ≤ T.xl b) && decide ((T.tayB b).t0 ≤ T.xl b ^ 2)) &&
    pivots2Pos (S.c0 + (T.tayB 0).base) (S.c0 + (T.tayB 1).base) S.e2

def pert (k : ℕ) : ℚ := 2 * T.width * S.K * S.sup k ^ 2

end Sliver2

/-- A constant Taylor branch bounds the potential at every point above its lower point. -/
private theorem const_branch_le {τ : TaylorBranch} (hτ : τ.valid = true) {xl : ℚ}
    (h0 : 0 ≤ xl) (ht : τ.t0 ≤ xl ^ 2) {x : ℝ} (hle : (xl : ℝ) ≤ x) (hx1 : x < 1) :
    (τ.base : ℝ) ≤ vTrue x := by
  have h := qeval_poly_le_vTrue hτ 0 xl 0 (ξ := 0) (by simpa using (show (0 : ℝ) ≤ xl by
    exact_mod_cast h0)) (by simpa using (show (τ.t0 : ℝ) ≤ (xl : ℝ) ^ 2 by exact_mod_cast ht))
    (by simpa using hle) hx1
  rw [qeval_TaylorBranch_poly] at h
  simpa using h

/-- `phiFn m x ^ 2 ≤ K ∑ sup_k² m_k²` on `[-1, 1]`. -/
private theorem sq_phiFn_le {S : SectorData} (hS : S.valid = true) (m : Fin S.K → ℝ) {x : ℝ}
    (hx : |x| ≤ 1) : S.phiFn m x ^ 2 ≤ (S.K : ℝ) * ∑ k : Fin S.K, (S.sup k : ℝ) ^ 2 * m k ^ 2 :=
  sq_lin_le _ (fun k => (S.sup k : ℝ)) (fun k => SectorData.abs_phiPoly_le hS k.2 hx) m

private theorem sum_sup_nonneg (S : SectorData) (m : Fin S.K → ℝ) :
    0 ≤ (S.K : ℝ) * ∑ k : Fin S.K, (S.sup k : ℝ) ^ 2 * m k ^ 2 :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity)

theorem Sliver4.bound {S : SectorData} (hS : S.valid = true) {T : Sliver4} (hT : T.check S = true)
    {G : ℝ → ℝ} (hGc : Continuous G)
    (hiPot : IntegrableOn (fun u => G u ^ 2 * (S.c0 + vTrue u)) (Ioo (0 : ℝ) 1))
    (m : Fin S.K → ℝ) :
    -(∑ k : Fin S.K, (T.pert S k : ℝ) * m k ^ 2) ≤
      ∫ s in (T.lo : ℝ)..((1 - primeThreeOffset) / 2), f4Integrand S G m s := by
  simp only [Sliver4.check, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hT
  obtain ⟨⟨⟨hlo0, hlo⟩, hbr⟩, hpiv⟩ := hT
  obtain ⟨haL, haH⟩ := primeThreeOffset_mem
  have haH1 : (aHiQ : ℝ) ≤ 3 / 5 := by norm_num [aHiQ]
  have haL1 : (1 / 2 : ℝ) ≤ aLoQ := by norm_num [aLoQ]
  have hlo0' : (0 : ℝ) ≤ T.lo := by exact_mod_cast hlo0
  have hlo' : (T.lo : ℝ) ≤ (1 - aHiQ) / 2 := by exact_mod_cast hlo
  set a := primeThreeOffset
  set C := (S.K : ℝ) * ∑ k : Fin S.K, (S.sup k : ℝ) ^ 2 * m k ^ 2
  have hC := sum_sup_nonneg S m
  have hpt : ∀ s ∈ Ioo (T.lo : ℝ) ((1 - a) / 2), -(4 * C) ≤ f4Integrand S G m s := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hlo0' hs.1
    have hb : ∀ b < 4, ∀ x : ℝ, (T.xl b : ℝ) ≤ x → x < 1 →
        (S.c0 + (T.tayB b).base : ℝ) ≤ S.c0 + vTrue x := fun b hb4 x hx hx1 => by
      obtain ⟨⟨⟨hv, _⟩, h0⟩, ht⟩ := hbr b hb4
      linarith [const_branch_le hv h0 ht hx hx1]
    have h0 := hb 0 (by norm_num) s (by simp only [Sliver4.xl]; linarith [hs.1]) (by linarith [hs.2])
    have h1 := hb 1 (by norm_num) (1 - s) (by simp only [Sliver4.xl]; push_cast; linarith [hs.2])
      (by linarith)
    have h2 := hb 2 (by norm_num) (a + s) (by simp only [Sliver4.xl]; push_cast; linarith [hs.1])
      (by linarith [hs.2])
    have h3 := hb 3 (by norm_num) (1 - a - s)
      (by simp only [Sliver4.xl]; push_cast; linarith [hs.2]) (by linarith)
    have hco := coercive4_of_pivots hpiv (by exact_mod_cast h0) (by exact_mod_cast h1)
      (by exact_mod_cast h2) (by exact_mod_cast h3)
    have hsl := tridiag4_sliver_ge hco (G s) (G (1 - s)) (G (a + s)) (G (1 - a - s))
      (S.phiFn m s) (S.phiFn m (1 - s)) (S.phiFn m (a + s)) (S.phiFn m (1 - a - s))
    have hv0 := sq_phiFn_le hS m (x := s) (abs_le.mpr ⟨by linarith, by linarith [hs.2]⟩)
    have hv1 := sq_phiFn_le hS m (x := 1 - s) (abs_le.mpr ⟨by linarith [hs.2], by linarith⟩)
    have hv2 := sq_phiFn_le hS m (x := a + s) (abs_le.mpr ⟨by linarith, by linarith [hs.2]⟩)
    have hv3 := sq_phiFn_le hS m (x := 1 - a - s) (abs_le.mpr ⟨by linarith [hs.2], by linarith⟩)
    simp only [f4Integrand]; push_cast at hsl
    linarith
  have hL4 : (T.lo : ℝ) ≤ (1 - a) / 2 := by linarith
  have hf := intervalIntegrable_f4Integrand (S := S) hGc hiPot m hlo0' hL4 le_rfl
  have hint := intervalIntegral_mono_on_Ioo' hL4 (continuous_const.intervalIntegrable _ _) hf hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hw : (1 - a) / 2 - T.lo ≤ (T.width : ℝ) := by simp only [Sliver4.width]; push_cast; linarith
  have hP : ∑ k : Fin S.K, (T.pert S k : ℝ) * m k ^ 2 = 4 * (T.width : ℝ) * C := by
    simp only [Sliver4.pert, C, Finset.mul_sum]; push_cast
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hP]
  nlinarith [mul_le_mul_of_nonneg_right hw (by linarith : (0 : ℝ) ≤ 4 * C)]

theorem Sliver2.bound {S : SectorData} (hS : S.valid = true) {T : Sliver2} (hT : T.check S = true)
    {G : ℝ → ℝ} (hGc : Continuous G)
    (hiPot : IntegrableOn (fun u => G u ^ 2 * (S.c0 + vTrue u)) (Ioo (0 : ℝ) 1))
    (m : Fin S.K → ℝ) :
    -(∑ k : Fin S.K, (T.pert S k : ℝ) * m k ^ 2) ≤
      ∫ u in (1 - primeThreeOffset)..(T.hi : ℝ), f2Integrand S G m u := by
  simp only [Sliver2.check, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hT
  obtain ⟨⟨⟨hhi0, hhi⟩, hbr⟩, hpiv⟩ := hT
  obtain ⟨haL, haH⟩ := primeThreeOffset_mem
  have haH1 : (aHiQ : ℝ) ≤ 3 / 5 := by norm_num [aHiQ]
  have hhi0' : (1 - aLoQ : ℝ) ≤ T.hi := by exact_mod_cast hhi0
  have hhi' : (T.hi : ℝ) ≤ 1 / 2 := by exact_mod_cast hhi
  set a := primeThreeOffset
  set C := (S.K : ℝ) * ∑ k : Fin S.K, (S.sup k : ℝ) ^ 2 * m k ^ 2
  have hC := sum_sup_nonneg S m
  have hpt : ∀ u ∈ Ioo (1 - a) (T.hi : ℝ), -(2 * C) ≤ f2Integrand S G m u := by
    intro u hu
    have hb : ∀ b < 2, ∀ x : ℝ, (T.xl b : ℝ) ≤ x → x < 1 →
        (S.c0 + (T.tayB b).base : ℝ) ≤ S.c0 + vTrue x := fun b hb2 x hx hx1 => by
      obtain ⟨⟨⟨hv, _⟩, h0⟩, ht⟩ := hbr b hb2
      linarith [const_branch_le hv h0 ht hx hx1]
    have h0 := hb 0 (by norm_num) u (by simp only [Sliver2.xl]; push_cast; linarith [hu.1])
      (by linarith [hu.2])
    have h1 := hb 1 (by norm_num) (1 - u) (by simp only [Sliver2.xl]; push_cast; linarith [hu.2])
      (by linarith [hu.1])
    have hco := coercive2_of_pivots hpiv (by exact_mod_cast h0) (by exact_mod_cast h1)
    have hsl := tridiag2_sliver_ge hco (G u) (G (1 - u)) (S.phiFn m u) (S.phiFn m (1 - u))
    have hv0 := sq_phiFn_le hS m (x := u) (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    have hv1 := sq_phiFn_le hS m (x := 1 - u)
      (abs_le.mpr ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    simp only [f2Integrand]; push_cast at hsl
    linarith
  have hle : 1 - a ≤ (T.hi : ℝ) := by linarith
  have hf := intervalIntegrable_f2Integrand (S := S) hGc hiPot m (by linarith) hle (by linarith)
  have hint := intervalIntegral_mono_on_Ioo' hle (continuous_const.intervalIntegrable _ _) hf hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hw : (T.hi : ℝ) - (1 - a) ≤ (T.width : ℝ) := by simp only [Sliver2.width]; push_cast; linarith
  have hP : ∑ k : Fin S.K, (T.pert S k : ℝ) * m k ^ 2 = 2 * (T.width : ℝ) * C := by
    simp only [Sliver2.pert, C, Finset.mul_sum]; push_cast
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hP]
  nlinarith [mul_le_mul_of_nonneg_right hw (by linarith : (0 : ℝ) ≤ 2 * C)]

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
