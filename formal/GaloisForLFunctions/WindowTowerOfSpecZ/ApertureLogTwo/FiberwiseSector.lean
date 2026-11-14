import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.FiberwiseCertificateAlgebra

/-!
# The data of one parity sector

A parity sector (`par = 1`: odd tests, degrees `1, 3, …`; `par = 0`: even tests, degrees
`0, 2, …`) fixes `K` retained half-window Legendre moments, the dual matrix `Λ`, the diagonal
offset `c₀`, the rational prime contacts `e₂, e₃`, and a rational approximation `a₀` of the
prime-three offset `a = log 3 / log 2 - 1`. The dual test is
`phiFn m x = ∑ₖ mₖ φₖ(x)`, `φₖ = ∑ᵣ Λ r k P_{2r + par}`, tabulated as `phiTab`.

`SectorData.valid` checks the table, the approximation `a₀`, and the shifted tables
`sh2 k (s) ≈ φₖ(a₀ + s)`, `sh3 k (s) ≈ φₖ(1 - a₀ - s)` with coefficient errors `shErr k`.
-/

open Real MeasureTheory Set Finset intervalIntegral
open scoped BigOperators

namespace GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo

open SelectivePositivityAndThresholdLaws

/-- All coefficients vanish. -/
def qzero (p : List ℚ) : Bool := p.all fun c => decide (c = 0)

theorem qeval_eq_zero_of_qzero : ∀ (p : List ℚ), qzero p = true → ∀ x : ℝ, qeval p x = 0
  | [], _, _ => rfl
  | c :: cs, h, x => by
    simp only [qzero, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := qeval_eq_zero_of_qzero cs h.2 x
    rw [qeval_cons, h.1, ih]; simp

theorem qeval_eq_of_qzero_sub {p q : List ℚ} (h : qzero (qsub p q) = true) (x : ℝ) :
    qeval p x = qeval q x := by
  have := qeval_eq_zero_of_qzero _ h x
  rw [qeval_qsub] at this; linarith

/-- Lower and upper rational bounds of the prime-three offset. -/
def aLoQ : ℚ := 5849625007211561814537389 / 10000000000000000000000000
def aHiQ : ℚ := 584962500721156181453739 / 1000000000000000000000000

theorem primeThreeOffset_mem : (aLoQ : ℝ) ≤ primeThreeOffset ∧ primeThreeOffset ≤ (aHiQ : ℝ) := by
  have h1 : (aLoQ : ℝ) = primeThreeShiftLo := by norm_num [aLoQ, primeThreeShiftLo]
  have h2 : (aHiQ : ℝ) = primeThreeShiftHi := by norm_num [aHiQ, primeThreeShiftHi]
  rw [h1, h2]
  exact primeThreeShift_bounds

/-- The data of one parity sector. -/
structure SectorData where
  K : ℕ
  par : ℕ
  rOrd : ℕ
  Λ : List (List ℚ)
  phiTab : List (List ℚ)
  c0 : ℚ
  e2 : ℚ
  e3 : ℚ
  a0 : ℚ
  δa : ℚ
  sh2 : List (List ℚ)
  sh3 : List (List ℚ)
  shErr : List ℚ

namespace SectorData

variable (S : SectorData)

def deg (r : ℕ) : ℕ := 2 * r + S.par

/-- `φₖ = ∑ᵣ Λ r k P_{deg r}` computed from the Legendre table. -/
def phiComputed (k : ℕ) : List ℚ :=
  ((List.range S.K).map fun r => qsmul (matQ S.Λ r k) (qleg (S.deg r))).foldr qadd []

def phiPoly (k : ℕ) : List ℚ := S.phiTab.getD k []

/-- Lipschitz constant of `φₖ` on `[-1, 1]` (Markov: `|P_d'| ≤ d(d+1)/2`). -/
def lip (k : ℕ) : ℚ :=
  ((List.range S.K).map fun r => |matQ S.Λ r k| * ((S.deg r : ℚ) * ((S.deg r : ℚ) + 1) / 2)).sum

/-- Supremum bound of `|φₖ|` on `[-1, 1]`. -/
def sup (k : ℕ) : ℚ := ((List.range S.K).map fun r => |matQ S.Λ r k|).sum

/-- The dual test. -/
noncomputable def phiFn (m : Fin S.K → ℝ) (x : ℝ) : ℝ := ∑ k : Fin S.K, m k * qeval (S.phiPoly k) x

/-- Half-window Legendre moments `mₖ = ∫₀¹ G P_{deg k}`. -/
noncomputable def moments (G : ℝ → ℝ) (k : Fin S.K) : ℝ := ∫ u in (0 : ℝ)..1, G u * legP (S.deg k) u

def validOffset : Bool :=
  decide (S.a0 - S.δa ≤ aLoQ) && decide (aHiQ ≤ S.a0 + S.δa) &&
    decide (0 ≤ S.δa) && decide (S.δa ≤ 1 / 100)

def validEntry (k : ℕ) : Bool :=
  qzero (qsub (S.phiPoly k) (S.phiComputed k)) &&
    decide (qabsSum (qsub (qcomp (S.phiPoly k) [S.a0, 1]) (S.sh2.getD k [])) ≤ S.shErr.getD k 0) &&
    decide (qabsSum (qsub (qcomp (S.phiPoly k) [1 - S.a0, -1]) (S.sh3.getD k [])) ≤
      S.shErr.getD k 0)

def valid : Bool :=
  S.validOffset && (List.range S.K).all S.validEntry

private theorem qeval_foldr_qadd (L : List (List ℚ)) (x : ℝ) :
    qeval (L.foldr qadd []) x = (L.map fun p => qeval p x).sum := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [List.foldr_cons, qeval_qadd, ih]

theorem qeval_phiComputed (k : ℕ) (x : ℝ) :
    qeval (S.phiComputed k) x = ∑ r : Fin S.K, (matQ S.Λ r k : ℝ) * legP (S.deg r) x := by
  rw [phiComputed, qeval_foldr_qadd, List.map_map]
  have hmap : List.map ((fun p => qeval p x) ∘ fun r => qsmul (matQ S.Λ r k) (qleg (S.deg r)))
      (List.range S.K) =
      List.map (fun r => (matQ S.Λ r k : ℝ) * legP (S.deg r) x) (List.range S.K) := by
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp_apply, qeval_qsmul, legP_eq_qeval_qleg]
  rw [hmap, list_sum_range_eq]

variable {S}

private theorem validEntry_of_valid (hS : S.valid = true) {k : ℕ} (hk : k < S.K) :
    S.validEntry k = true := by
  have h := (Bool.and_eq_true _ _).mp hS
  exact List.all_eq_true.mp h.2 k (List.mem_range.mpr hk)

theorem qeval_phiPoly (hS : S.valid = true) {k : ℕ} (hk : k < S.K) (x : ℝ) :
    qeval (S.phiPoly k) x = ∑ r : Fin S.K, (matQ S.Λ r k : ℝ) * legP (S.deg r) x := by
  have hk' := validEntry_of_valid hS hk
  simp only [validEntry, Bool.and_eq_true] at hk'
  rw [qeval_eq_of_qzero_sub hk'.1.1, qeval_phiComputed]

theorem abs_phiPoly_sub_le (hS : S.valid = true) {k : ℕ} (hk : k < S.K) {x y : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    |qeval (S.phiPoly k) x - qeval (S.phiPoly k) y| ≤ (S.lip k : ℝ) * |x - y| := by
  rw [qeval_phiPoly hS hk, qeval_phiPoly hS hk, ← Finset.sum_sub_distrib, lip,
    list_sum_range_eq, Rat.cast_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [← mul_sub, abs_mul]
  push_cast
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_legP_sub_le hx hy _) (abs_nonneg _)

theorem abs_phiPoly_le (hS : S.valid = true) {k : ℕ} (hk : k < S.K) {x : ℝ} (hx : |x| ≤ 1) :
    |qeval (S.phiPoly k) x| ≤ (S.sup k : ℝ) := by
  rw [qeval_phiPoly hS hk, sup, list_sum_range_eq, Rat.cast_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [abs_mul]; push_cast
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_legP_le_one hx _)

theorem abs_sub_sh2_le (hS : S.valid = true) {k : ℕ} (hk : k < S.K) {s : ℝ} (hs : |s| ≤ 1) :
    |qeval (S.phiPoly k) (S.a0 + s) - qeval (S.sh2.getD k []) s| ≤ (S.shErr.getD k 0 : ℝ) := by
  have hk' := validEntry_of_valid hS hk
  simp only [validEntry, Bool.and_eq_true, decide_eq_true_eq] at hk'
  have hb := abs_qeval_le_qabsSum (qsub (qcomp (S.phiPoly k) [S.a0, 1]) (S.sh2.getD k [])) hs
  rw [qeval_qsub, qeval_qcomp_affine] at hb
  have h' : (qabsSum (qsub (qcomp (S.phiPoly k) [S.a0, 1]) (S.sh2.getD k [])) : ℝ) ≤
      (S.shErr.getD k 0 : ℝ) := Rat.cast_le.mpr hk'.1.2
  have he : ((S.a0 : ℚ) : ℝ) + ((1 : ℚ) : ℝ) * s = S.a0 + s := by push_cast; ring
  rw [he] at hb
  exact hb.trans h'

theorem abs_sub_sh3_le (hS : S.valid = true) {k : ℕ} (hk : k < S.K) {s : ℝ} (hs : |s| ≤ 1) :
    |qeval (S.phiPoly k) (1 - S.a0 - s) - qeval (S.sh3.getD k []) s| ≤
      (S.shErr.getD k 0 : ℝ) := by
  have hk' := validEntry_of_valid hS hk
  simp only [validEntry, Bool.and_eq_true, decide_eq_true_eq] at hk'
  have hb := abs_qeval_le_qabsSum (qsub (qcomp (S.phiPoly k) [1 - S.a0, -1]) (S.sh3.getD k [])) hs
  rw [qeval_qsub, qeval_qcomp_affine] at hb
  have h' : (qabsSum (qsub (qcomp (S.phiPoly k) [1 - S.a0, -1]) (S.sh3.getD k [])) : ℝ) ≤
      (S.shErr.getD k 0 : ℝ) := Rat.cast_le.mpr hk'.2
  have he : ((1 - S.a0 : ℚ) : ℝ) + ((-1 : ℚ) : ℝ) * s = 1 - S.a0 - s := by push_cast; ring
  rw [he] at hb
  exact hb.trans h'

theorem abs_offset_sub_le (hS : S.valid = true) :
    |primeThreeOffset - S.a0| ≤ (S.δa : ℝ) ∧ (S.δa : ℝ) ≤ 1 / 100 := by
  have ho : S.validOffset = true := ((Bool.and_eq_true _ _).mp hS).1
  simp only [validOffset, Bool.and_eq_true, decide_eq_true_eq] at ho
  obtain ⟨⟨⟨h1, h2⟩, _⟩, h4⟩ := ho
  have h1' : (S.a0 : ℝ) - S.δa ≤ aLoQ := by rw [← Rat.cast_sub]; exact Rat.cast_le.mpr h1
  have h2' : (aHiQ : ℝ) ≤ (S.a0 : ℝ) + S.δa := by rw [← Rat.cast_add]; exact Rat.cast_le.mpr h2
  obtain ⟨ha1, ha2⟩ := primeThreeOffset_mem
  have hlo : (S.a0 : ℝ) - S.δa ≤ primeThreeOffset := h1'.trans ha1
  have hhi : primeThreeOffset ≤ (S.a0 : ℝ) + S.δa := ha2.trans h2'
  have h4' : (S.δa : ℝ) ≤ 1 / 100 := by
    have := Rat.cast_le (K := ℝ).mpr h4; push_cast at this; exact this
  exact ⟨abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩, h4'⟩

/-- Exact dual pairing `∫₀¹ G · phiFn m = mᵀ Λ m` at the half-window moments of `G`. -/
theorem integral_mul_phiFn (hS : S.valid = true) {G : ℝ → ℝ} (hG : Continuous G) :
    (∫ u in (0 : ℝ)..1, G u * S.phiFn (S.moments G) u) = quadR S.K S.Λ (S.moments G) := by
  have hfn : (fun u => G u * S.phiFn (S.moments G) u) =
      fun u => ∑ k : Fin S.K, ∑ r : Fin S.K,
        (S.moments G k * (matQ S.Λ r k : ℝ)) * (G u * legP (S.deg r) u) := funext fun u => by
    rw [phiFn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [qeval_phiPoly hS k.2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => by ring
  have hi1 : ∀ k ∈ (Finset.univ : Finset (Fin S.K)),
      IntervalIntegrable (fun u => ∑ r : Fin S.K,
        (S.moments G k * (matQ S.Λ r k : ℝ)) * (G u * legP (S.deg r) u)) volume 0 1 :=
    fun k _ => (continuous_finsetSum _ fun r _ =>
      continuous_const.mul (hG.mul (continuous_legP _))).intervalIntegrable 0 1
  rw [hfn, intervalIntegral.integral_finsetSum hi1]
  have hinner : ∀ k : Fin S.K,
      (∫ u in (0 : ℝ)..1, ∑ r : Fin S.K,
        (S.moments G k * (matQ S.Λ r k : ℝ)) * (G u * legP (S.deg r) u)) =
      ∑ r : Fin S.K, (S.moments G k * (matQ S.Λ r k : ℝ)) * S.moments G r := fun k => by
    have hi2 : ∀ r ∈ (Finset.univ : Finset (Fin S.K)),
        IntervalIntegrable (fun u =>
          (S.moments G k * (matQ S.Λ r k : ℝ)) * (G u * legP (S.deg r) u)) volume 0 1 :=
      fun r _ => (continuous_const.mul (hG.mul (continuous_legP _))).intervalIntegrable 0 1
    rw [intervalIntegral.integral_finsetSum hi2]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [intervalIntegral.integral_const_mul]; rfl
  rw [Finset.sum_congr rfl fun k _ => hinner k, quadR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => by ring

end SectorData

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
