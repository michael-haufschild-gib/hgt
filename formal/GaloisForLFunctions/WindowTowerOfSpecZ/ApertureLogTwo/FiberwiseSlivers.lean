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
def xl (b : ℕ) : ℚ :=
  if b = 0 then T.lo
  else if b = 1 then 1 - (1 - aLoQ) / 2
  else if b = 2 then aLoQ + T.lo
  else if b = 3 then 1 - aHiQ - (1 - aLoQ) / 2
  else 0

def width : ℚ := (1 - aLoQ) / 2 - T.lo

def branchOK (b : ℕ) : Bool :=
  (T.tayB b).valid && decide (0 < (T.tayB b).om) &&
    decide (0 ≤ T.xl b) && decide ((T.tayB b).t0 ≤ T.xl b ^ 2)

def check : Bool :=
  decide (0 ≤ T.lo) && decide (T.lo ≤ (1 - aHiQ) / 2) &&
    (List.range 4).all (fun b => T.branchOK b) &&
    pivots4Pos (S.c0 + (T.tayB 0).base) (S.c0 + (T.tayB 1).base) (S.c0 + (T.tayB 2).base)
      (S.c0 + (T.tayB 3).base) S.e2 S.e3

def pert (k : ℕ) : ℚ := 4 * T.width * S.K * S.sup k ^ 2

end Sliver4

namespace Sliver2

variable (S : SectorData) (T : Sliver2)

def tayB (b : ℕ) : TaylorBranch := T.tay.getD b ⟨0, 0, 0, 1, 0⟩

def xl (b : ℕ) : ℚ :=
  if b = 0 then 1 - aHiQ
  else if b = 1 then 1 - T.hi
  else 0

def width : ℚ := T.hi - (1 - aHiQ)

def branchOK (b : ℕ) : Bool :=
  (T.tayB b).valid && decide (0 < (T.tayB b).om) &&
    decide (0 ≤ T.xl b) && decide ((T.tayB b).t0 ≤ T.xl b ^ 2)

def check : Bool :=
  decide (1 - aLoQ ≤ T.hi) && decide (T.hi ≤ 1 / 2) &&
    (List.range 2).all (fun b => T.branchOK b) &&
    pivots2Pos (S.c0 + (T.tayB 0).base) (S.c0 + (T.tayB 1).base) S.e2

def pert (k : ℕ) : ℚ := 2 * T.width * S.K * S.sup k ^ 2

end Sliver2

/-- A constant Taylor branch bounds the potential at every point above its lower point. -/
private theorem const_branch_le {τ : TaylorBranch} (hτ : τ.valid = true) {xl : ℚ}
    (h0 : 0 ≤ xl) (ht : τ.t0 ≤ xl ^ 2) {x : ℝ} (hle : (xl : ℝ) ≤ x) (hx1 : x < 1) :
    (τ.base : ℝ) ≤ vTrue x := by
  have h0' : (0 : ℝ) ≤ (xl : ℝ) + (0 : ℚ) * (0 : ℝ) := by
    rw [Rat.cast_zero, mul_zero, add_zero]; exact Rat.cast_nonneg.mpr h0
  have ht' : (τ.t0 : ℝ) ≤ ((xl : ℝ) + (0 : ℚ) * (0 : ℝ)) ^ 2 := by
    rw [Rat.cast_zero, mul_zero, add_zero, ← Rat.cast_pow]; exact Rat.cast_le.mpr ht
  have hle' : (xl : ℝ) + (0 : ℚ) * (0 : ℝ) ≤ x := by
    rw [Rat.cast_zero, mul_zero, add_zero]; exact hle
  have h := qeval_poly_le_vTrue hτ 0 xl 0 (ξ := 0) h0' ht' hle' hx1
  have hev : qeval (τ.poly 0 xl 0) 0 = τ.base := by
    simp only [TaylorBranch.poly, tayTail, qadd, qeval]; ring
  rwa [hev] at h

/-- `phiFn m x ^ 2 ≤ K ∑ sup_k² m_k²` on `[-1, 1]`. -/
private theorem sq_phiFn_le {S : SectorData} (hS : S.valid = true) (m : Fin S.K → ℝ) {x : ℝ}
    (hx : |x| ≤ 1) : S.phiFn m x ^ 2 ≤ (S.K : ℝ) * ∑ k : Fin S.K, (S.sup k : ℝ) ^ 2 * m k ^ 2 :=
  sq_lin_le _ (fun k => (S.sup k : ℝ)) (fun k => SectorData.abs_phiPoly_le hS k.2 hx) m

private theorem sum_sup_nonneg (S : SectorData) (m : Fin S.K → ℝ) :
    0 ≤ (S.K : ℝ) * ∑ k : Fin S.K, (S.sup k : ℝ) ^ 2 * m k ^ 2 :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity)

theorem aLoQ_HiQ_bounds : (1 / 2 : ℝ) ≤ aLoQ ∧ (aHiQ : ℝ) ≤ 3 / 5 := by
  constructor <;> norm_num [aLoQ, aHiQ]

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
  obtain ⟨haL1, haH1⟩ := aLoQ_HiQ_bounds
  have hlo0' : (0 : ℝ) ≤ T.lo := Rat.cast_nonneg.mpr hlo0
  have hlo' : (T.lo : ℝ) ≤ (1 - (aHiQ : ℝ)) / 2 := by
    have := Rat.cast_le (K := ℝ).mpr hlo
    simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat] at this; exact this
  have hxl0 : (T.xl 0 : ℝ) = T.lo := by simp only [Sliver4.xl, ↓reduceIte]
  have hxl1 : (T.xl 1 : ℝ) = 1 - (1 - (aLoQ : ℝ)) / 2 := by
    simp only [Sliver4.xl, OfNat.one_ne_zero, ↓reduceIte,
      Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  have hxl2 : (T.xl 2 : ℝ) = (aLoQ : ℝ) + T.lo := by
    simp only [Sliver4.xl, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte, Rat.cast_add]
  have hxl3 : (T.xl 3 : ℝ) = 1 - (aHiQ : ℝ) - (1 - (aLoQ : ℝ)) / 2 := by
    have : (3 : ℕ) ≠ 2 := by decide
    simp only [Sliver4.xl, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, this, ↓reduceIte,
      Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  have hwid : (T.width : ℝ) = (1 - (aLoQ : ℝ)) / 2 - T.lo := by
    simp only [Sliver4.width, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  generalize (aLoQ : ℝ) = aL, (aHiQ : ℝ) = aH at haL haH haL1 haH1 hlo' hxl1 hxl2 hxl3 hwid
  set a := primeThreeOffset
  set C := (S.K : ℝ) * ∑ k : Fin S.K, (S.sup k : ℝ) ^ 2 * m k ^ 2
  have hC := sum_sup_nonneg S m
  have hpt : ∀ s ∈ Ioo (T.lo : ℝ) ((1 - a) / 2), -(4 * C) ≤ f4Integrand S G m s := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hlo0' hs.1
    have hb : ∀ b < 4, ∀ x : ℝ, (T.xl b : ℝ) ≤ x → x < 1 →
        ((S.c0 + (T.tayB b).base : ℚ) : ℝ) ≤ S.c0 + vTrue x := fun b hb4 x hx hx1 => by
      have hb_ok := hbr b hb4
      simp only [Sliver4.branchOK, Bool.and_eq_true, decide_eq_true_eq] at hb_ok
      obtain ⟨⟨⟨hv, _⟩, h0⟩, ht⟩ := hb_ok
      have := const_branch_le hv h0 ht hx hx1
      rw [Rat.cast_add]; linarith only [this]
    have h0 := hb 0 (by norm_num) s (by rw [hxl0]; exact hs.1.le)
      (by linarith only [hs.2, haL, haL1])
    have h1 := hb 1 (by norm_num) (1 - s)
      (by rw [hxl1]; linarith only [hs.2, haL]) (by linarith only [hs0])
    have h2 := hb 2 (by norm_num) (a + s)
      (by rw [hxl2]; linarith only [hs.1, haL]) (by linarith only [hs.2, haH, haH1])
    have h3 := hb 3 (by norm_num) (1 - a - s)
      (by rw [hxl3]; linarith only [hs.2, haL, haH]) (by linarith only [hs0, haL, haL1])
    have hco := coercive4_of_pivots hpiv h0 h1 h2 h3
    have hsl : -(S.phiFn m s ^ 2 + S.phiFn m (1 - s) ^ 2 + S.phiFn m (a + s) ^ 2 +
        S.phiFn m (1 - a - s) ^ 2) ≤ f4Integrand S G m s :=
      tridiag4_sliver_ge hco (G s) (G (1 - s)) (G (a + s)) (G (1 - a - s))
        (S.phiFn m s) (S.phiFn m (1 - s)) (S.phiFn m (a + s)) (S.phiFn m (1 - a - s))
    have hv0 : S.phiFn m s ^ 2 ≤ C := sq_phiFn_le hS m (x := s)
      (abs_le.mpr ⟨by linarith only [hs0], by linarith only [hs.2, haL, haL1]⟩)
    have hv1 : S.phiFn m (1 - s) ^ 2 ≤ C := sq_phiFn_le hS m (x := 1 - s)
      (abs_le.mpr ⟨by linarith only [hs.2, haL, haL1], by linarith only [hs0]⟩)
    have hv2 : S.phiFn m (a + s) ^ 2 ≤ C := sq_phiFn_le hS m (x := a + s)
      (abs_le.mpr ⟨by linarith only [hs0, haL, haL1], by linarith only [hs.2, haH, haH1]⟩)
    have hv3 : S.phiFn m (1 - a - s) ^ 2 ≤ C := sq_phiFn_le hS m (x := 1 - a - s)
      (abs_le.mpr ⟨by linarith only [hs.2, haH, haH1], by linarith only [hs0, haL, haL1]⟩)
    have hv := add_le_add (add_le_add (add_le_add hv0 hv1) hv2) hv3
    exact (by linarith only [hv] : -(4 * C) ≤ _).trans hsl
  have hL4 : (T.lo : ℝ) ≤ (1 - a) / 2 := by linarith only [hlo', haH]
  have hf := intervalIntegrable_f4Integrand (S := S) hGc hiPot m hlo0' hL4 le_rfl
  have hint := intervalIntegral_mono_on_Ioo' hL4 (continuous_const.intervalIntegrable _ _) hf hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hw : (1 - a) / 2 - T.lo ≤ (T.width : ℝ) := by rw [hwid]; linarith only [haL]
  have hP : ∑ k : Fin S.K, (T.pert S k : ℝ) * m k ^ 2 = 4 * (T.width : ℝ) * C := by
    simp only [Sliver4.pert, C, Finset.mul_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_ofNat]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hP]
  have hmul := mul_le_mul_of_nonneg_right hw (by positivity : (0 : ℝ) ≤ 4 * C)
  linarith only [hint, hmul]

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
  obtain ⟨-, haH1⟩ := aLoQ_HiQ_bounds
  have hhi0' : 1 - (aLoQ : ℝ) ≤ T.hi := by
    have := Rat.cast_le (K := ℝ).mpr hhi0
    simp only [Rat.cast_sub, Rat.cast_one] at this; exact this
  have hhi' : (T.hi : ℝ) ≤ 1 / 2 := by
    have := Rat.cast_le (K := ℝ).mpr hhi
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at this; exact this
  have hxl0 : (T.xl 0 : ℝ) = 1 - (aHiQ : ℝ) := by
    simp only [Sliver2.xl, ↓reduceIte, Rat.cast_sub, Rat.cast_one]
  have hxl1 : (T.xl 1 : ℝ) = 1 - (T.hi : ℝ) := by
    simp only [Sliver2.xl, OfNat.one_ne_zero, ↓reduceIte, Rat.cast_sub, Rat.cast_one]
  have hwid : (T.width : ℝ) = (T.hi : ℝ) - (1 - (aHiQ : ℝ)) := by
    simp only [Sliver2.width, Rat.cast_sub, Rat.cast_one]
  generalize (aLoQ : ℝ) = aL, (aHiQ : ℝ) = aH at haL haH haH1 hhi0' hxl0 hwid
  set a := primeThreeOffset
  set C := (S.K : ℝ) * ∑ k : Fin S.K, (S.sup k : ℝ) ^ 2 * m k ^ 2
  have hC := sum_sup_nonneg S m
  have hpt : ∀ u ∈ Ioo (1 - a) (T.hi : ℝ), -(2 * C) ≤ f2Integrand S G m u := by
    intro u hu
    have hb : ∀ b < 2, ∀ x : ℝ, (T.xl b : ℝ) ≤ x → x < 1 →
        ((S.c0 + (T.tayB b).base : ℚ) : ℝ) ≤ S.c0 + vTrue x := fun b hb2 x hx hx1 => by
      have hb_ok := hbr b hb2
      simp only [Sliver2.branchOK, Bool.and_eq_true, decide_eq_true_eq] at hb_ok
      obtain ⟨⟨⟨hv, _⟩, h0⟩, ht⟩ := hb_ok
      have := const_branch_le hv h0 ht hx hx1
      rw [Rat.cast_add]; linarith only [this]
    have h0 := hb 0 (by norm_num) u (by rw [hxl0]; linarith only [hu.1, haH])
      (by linarith only [hu.2, hhi'])
    have h1 := hb 1 (by norm_num) (1 - u) (by rw [hxl1]; linarith only [hu.2])
      (by linarith only [hu.1, haH, haH1])
    have hco := coercive2_of_pivots hpiv h0 h1
    have hsl : -(S.phiFn m u ^ 2 + S.phiFn m (1 - u) ^ 2) ≤ f2Integrand S G m u :=
      tridiag2_sliver_ge hco (G u) (G (1 - u)) (S.phiFn m u) (S.phiFn m (1 - u))
    have hv0 : S.phiFn m u ^ 2 ≤ C := sq_phiFn_le hS m (x := u)
      (abs_le.mpr ⟨by linarith only [hu.1, haH, haH1], by linarith only [hu.2, hhi']⟩)
    have hv1 : S.phiFn m (1 - u) ^ 2 ≤ C := sq_phiFn_le hS m (x := 1 - u)
      (abs_le.mpr ⟨by linarith only [hu.2, hhi'], by linarith only [hu.1, haH, haH1]⟩)
    have hv := add_le_add hv0 hv1
    exact (by linarith only [hv] : -(2 * C) ≤ _).trans hsl
  have hle : 1 - a ≤ (T.hi : ℝ) := by linarith only [hhi0', haL]
  have hf := intervalIntegrable_f2Integrand (S := S) hGc hiPot m
    (by linarith only [haH, haH1]) hle (by linarith only [hhi'])
  have hint := intervalIntegral_mono_on_Ioo' hle (continuous_const.intervalIntegrable _ _) hf hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hw : (T.hi : ℝ) - (1 - a) ≤ (T.width : ℝ) := by rw [hwid]; linarith only [haH]
  have hP : ∑ k : Fin S.K, (T.pert S k : ℝ) * m k ^ 2 = 2 * (T.width : ℝ) * C := by
    simp only [Sliver2.pert, C, Finset.mul_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_ofNat]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hP]
  have hmul := mul_le_mul_of_nonneg_right hw (by positivity : (0 : ℝ) ≤ 2 * C)
  linarith only [hint, hmul]

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
