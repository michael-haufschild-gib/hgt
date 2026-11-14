import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.FiberwiseSector

/-!
# Four-branch subintervals of the folded half window

On `s ∈ (0, (1 - a)/2)` the folded Weil form couples `G` at `s, 1 - s, a + s, 1 - a - s` through
the tridiagonal fiber with diagonal `c₀ + vTrue` and contacts `e₂, e₃, e₂`. On a subinterval
`s = sa + ds ξ`, `ξ ∈ (0, 1)`, a rational certificate `P4Sub` consists of

* Taylor minorants of the potential with rounded polynomials `Ṽ_b` and a pivot check,
* polynomial witnesses `W b i` (one per branch and moment),
* a dominating rational matrix `Qhat` and a dominating diagonal `pertHat`.

`P4Sub.bound` turns `P4Sub.check = true` into
`∫_{sa}^{sa+ds} f4Integrand ≥ -mᵀ Qhat m - ∑ pertHat_k m_k²` for every moment vector `m`.
The exact matrix `qMat` is the `ξ`-integral of the completed squares; its rounded dual sources
`vv` carry the coefficient errors `eta`, paid in `pertHat`.
-/

open Real MeasureTheory Set Finset intervalIntegral
open scoped BigOperators

namespace GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo

open SelectivePositivityAndThresholdLaws

/-- The four-branch fiber integrand, `a = primeThreeOffset`. -/
noncomputable def f4Integrand (S : SectorData) (G : ℝ → ℝ) (m : Fin S.K → ℝ) (s : ℝ) : ℝ :=
  tridiag4Form (S.c0 + vTrue s) (S.c0 + vTrue (1 - s)) (S.c0 + vTrue (primeThreeOffset + s))
      (S.c0 + vTrue (1 - primeThreeOffset - s)) S.e2 S.e3
      (G s) (G (1 - s)) (G (primeThreeOffset + s)) (G (1 - primeThreeOffset - s)) -
    2 * (G s * S.phiFn m s + G (1 - s) * S.phiFn m (1 - s) +
      G (primeThreeOffset + s) * S.phiFn m (primeThreeOffset + s) +
      G (1 - primeThreeOffset - s) * S.phiFn m (1 - primeThreeOffset - s))

/-! ### Generic integration lemmas -/

theorem intervalIntegral_mono_on_Ioo' {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hpt : ∀ x ∈ Ioo a b, f x ≤ g x) : (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_mono_on (hf.1.mono_set Ioo_subset_Ioc_self)
    (hg.1.mono_set Ioo_subset_Ioc_self) measurableSet_Ioo hpt

/-- A continuous pointwise minorant in the unit variable integrates to a lower bound. -/
theorem integral_ge_of_unit_minorant {f L : ℝ → ℝ} (hL : Continuous L) {sa ds : ℝ}
    (hds : 0 < ds) (hf : IntervalIntegrable f volume sa (sa + ds))
    (hpt : ∀ ξ ∈ Ioo (0 : ℝ) 1, L ξ ≤ f (sa + ds * ξ)) :
    ds * (∫ ξ in (0 : ℝ)..1, L ξ) ≤ ∫ s in sa..(sa + ds), f s := by
  set L' : ℝ → ℝ := fun s => L ((s - sa) / ds)
  have hL' : Continuous L' := hL.comp ((continuous_id.sub continuous_const).div_const _)
  have hmono := intervalIntegral_mono_on_Ioo' (by linarith) (hL'.intervalIntegrable _ _) hf
    (fun s hs => by
      have hξ : (s - sa) / ds ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos (by linarith [hs.1]) hds, (div_lt_one hds).mpr (by linarith [hs.2])⟩
      have h := hpt _ hξ
      rwa [show sa + ds * ((s - sa) / ds) = s by field_simp; ring] at h)
  have hcv : (∫ ξ in (0 : ℝ)..1, L ξ) = ds⁻¹ * ∫ s in sa..(sa + ds), L' s := by
    have h := intervalIntegral.integral_comp_mul_add L' (a := 0) (b := 1) hds.ne' sa
    simp only [mul_zero, zero_add, mul_one, smul_eq_mul] at h
    rw [add_comm ds sa] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    simp only [L']; congr 1; field_simp; ring
  rw [hcv, ← mul_assoc, mul_inv_cancel₀ hds.ne', one_mul]
  exact hmono

/-! ### Integrability of the four-branch integrand -/

/-- The potential part is integrable on every subinterval of `[0, (1 - a)/2]`. -/
theorem intervalIntegrable_f4Integrand {S : SectorData} {G : ℝ → ℝ} (hGc : Continuous G)
    (hiPot : IntegrableOn (fun u => G u ^ 2 * (S.c0 + vTrue u)) (Ioo (0 : ℝ) 1))
    (m : Fin S.K → ℝ) {α β : ℝ} (h0 : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ (1 - primeThreeOffset) / 2) :
    IntervalIntegrable (f4Integrand S G m) volume α β := by
  obtain ⟨ha_lo, ha_hi⟩ := primeThreeOffset_bounds
  set a := primeThreeOffset
  let H : ℝ → ℝ := fun u => (S.c0 + vTrue u) * G u ^ 2
  have hH : IntegrableOn H (Icc (0 : ℝ) 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioo).mpr (hiPot.congr_fun (fun u _ => mul_comm _ _)
      measurableSet_Ioo)
  have hii : ∀ p q : ℝ, 0 ≤ p → p ≤ q → q ≤ 1 → IntervalIntegrable H volume p q :=
    fun p q hp hpq hq => (intervalIntegrable_iff_integrableOn_Icc_of_le hpq).mpr
      (hH.mono_set (Icc_subset_Icc hp hq))
  have i0 : IntervalIntegrable H volume α β := hii α β h0 hαβ (by linarith)
  have i1 : IntervalIntegrable (fun s => H (1 - s)) volume α β := by
    have h := ((hii (1 - β) (1 - α) (by linarith) (by linarith) (by linarith)).comp_sub_left 1).symm
    simpa using h
  have i2 : IntervalIntegrable (fun s => H (a + s)) volume α β := by
    have h := (hii (a + α) (a + β) (by linarith) (by linarith) (by linarith)).comp_add_left a
    simpa using h
  have i3 : IntervalIntegrable (fun s => H (1 - a - s)) volume α β := by
    have h := ((hii (1 - a - β) (1 - a - α) (by linarith) (by linarith)
      (by linarith)).comp_sub_left (1 - a)).symm
    simpa using h
  have hpc : Continuous (S.phiFn m) :=
    continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_qeval _)
  let R : ℝ → ℝ := fun s =>
    2 * S.e2 * G s * G (1 - s) + 2 * S.e3 * G (1 - s) * G (a + s) +
      2 * S.e2 * G (a + s) * G (1 - a - s) -
    2 * (G s * S.phiFn m s + G (1 - s) * S.phiFn m (1 - s) + G (a + s) * S.phiFn m (a + s) +
      G (1 - a - s) * S.phiFn m (1 - a - s))
  have hR : Continuous R := by dsimp only [R]; fun_prop
  have hf : f4Integrand S G m = fun s =>
      (((H s + H (1 - s)) + H (a + s)) + H (1 - a - s)) + R s := by
    funext s; simp only [f4Integrand, tridiag4Form, H, R, a]; ring
  rw [hf]
  exact (((i0.add i1).add i2).add i3).add (hR.intervalIntegrable α β)

/-! ### Four-branch subinterval certificates -/

/-- One four-branch subinterval `[sa, sa + ds]` with its rational certificate. -/
structure P4Sub where
  sa : ℚ
  ds : ℚ
  tay : List TaylorBranch
  Vt : List (List ℚ)
  W : List (List (List ℚ))
  Qhat : List (List ℚ)
  pertHat : List ℚ

/-- Rounding grid of the dual sources. -/
def roundGrid : ℕ := 10 ^ 30

/-- Penalty of the witnesses against source perturbations. -/
def pen : ℚ := 1 / 10 ^ 22

/-- Gram pairing truncated to the first `N` Hilbert rows. -/
def gramN (N : ℕ) (p q : List ℚ) : ℚ := dotQ p (hilbVec N q)

private theorem dotQ_append_left : ∀ (p l₁ l₂ : List ℚ), p.length ≤ l₁.length →
    dotQ p (l₁ ++ l₂) = dotQ p l₁
  | [], _, _, _ => by simp [dotQ]
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, l₂, h => by
    simp only [List.cons_append, dotQ]
    rw [dotQ_append_left as bs l₂ (by simpa using h)]

theorem gramN_eq {N : ℕ} {p : List ℚ} (h : p.length ≤ N) (q : List ℚ) :
    gramN N p q = dotQ p (hilbVec p.length q) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [gramN, hilbVec, List.range_add, List.map_append]
  exact dotQ_append_left _ _ _ (by simp)

theorem integral_lin_mul_lin_gramN {K N : ℕ} (A B : ℕ → List ℚ) (hA : ∀ i < K, (A i).length ≤ N)
    (m : Fin K → ℝ) :
    (∫ ξ in (0 : ℝ)..1, linQ A m ξ * linQ B m ξ) =
      ∑ i : Fin K, ∑ j : Fin K, (gramN N (A i) (B j) : ℝ) * m i * m j := by
  rw [integral_lin_mul_lin]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [gramN_eq (hA i i.2)]

namespace P4Sub

variable (S : SectorData) (D : P4Sub)

def tayB (b : ℕ) : TaylorBranch := D.tay.getD b ⟨0, 0, 0, 1, 0⟩
def VtB (b : ℕ) : List ℚ := D.Vt.getD b []
def WB (b i : ℕ) : List ℚ := (D.W.getD b []).getD i []

/-- Lower affine argument `x₀ + x₁ ξ` of the potential on branch `b`. -/
def lowAff : ℕ → ℚ × ℚ
  | 0 => (D.sa, D.ds)
  | 1 => (1 - D.sa, -D.ds)
  | 2 => (aLoQ + D.sa, D.ds)
  | _ => (1 - aHiQ - D.sa, -D.ds)

/-- Exact dual source polynomial in `ξ` on branch `b`. -/
def vvExact : ℕ → ℕ → List ℚ
  | 0, k => qcomp (S.phiPoly k) [D.sa, D.ds]
  | 1, k => qcomp (S.phiPoly k) [1 - D.sa, -D.ds]
  | 2, k => qcomp (S.sh2.getD k []) [D.sa, D.ds]
  | _, k => qcomp (S.sh3.getD k []) [D.sa, D.ds]

/-- Rounding of a coefficient list to the grid. -/
def roundList (p : List ℚ) : List ℚ := p.map (qroundD roundGrid)

/-- Coefficient error of the rounded source plus the shift and offset errors. -/
def etaOf (b k : ℕ) (ex : List ℚ) : ℚ :=
  qabsSum (qsub ex (roundList ex)) + if 2 ≤ b then S.shErr.getD k 0 + S.δa * S.lip k else 0

/-- Tridiagonal action `(D(ξ) w)_b` with diagonal `c₀ + Ṽ_b`, on the witness family `w`. -/
def mwOf (w : ℕ → List ℚ) : ℕ → List ℚ
  | 0 => qadd (qmul (qadd [S.c0] (D.VtB 0)) (w 0)) (qsmul S.e2 (w 1))
  | 1 => qadd (qadd (qsmul S.e2 (w 0)) (qmul (qadd [S.c0] (D.VtB 1)) (w 1))) (qsmul S.e3 (w 2))
  | 2 => qadd (qadd (qsmul S.e3 (w 1)) (qmul (qadd [S.c0] (D.VtB 2)) (w 2))) (qsmul S.e2 (w 3))
  | _ => qadd (qsmul S.e2 (w 2)) (qmul (qadd [S.c0] (D.VtB 3)) (w 3))

def mw (b i : ℕ) : List ℚ := mwOf S D (fun b' => D.WB b' i) b
def vv (b k : ℕ) : List ℚ := roundList (vvExact S D b k)
def hh (b i : ℕ) : List ℚ :=
  qadd (qsub (qsmul 2 (vv S D b i)) (mw S D b i)) (qsmul pen (D.WB b i))
def er (b i : ℕ) : List ℚ := qsub (mw S D b i) (vv S D b i)
def eta (b k : ℕ) : ℚ := etaOf S b k (vvExact S D b k)

/-- The exact quadratic form of the completed squares on the subinterval. -/
def qMat : List (List ℚ) :=
  tabQ S.K fun i j => D.ds * ((List.range 4).map fun b =>
    (gramN 7 (D.WB b i) (hh S D b j) + gramN 7 (D.WB b j) (hh S D b i)) / 2 +
      gramN 32 (er S D b i) (er S D b j)).sum

/-- The diagonal paying the perturbations of the sources. -/
def pert (k : ℕ) : ℚ :=
  D.ds * (16 + 10 ^ 22) * S.K * ((List.range 4).map fun b => eta S D b k ^ 2).sum

/-- Table of `f b i` over `b < 4`, `i < K`. -/
def tab4 (K : ℕ) (f : ℕ → ℕ → List ℚ) : List (List (List ℚ)) :=
  (List.range 4).map fun b => (List.range K).map fun i => f b i

def get4 (T : List (List (List ℚ))) (b i : ℕ) : List ℚ := (T.getD b []).getD i []

theorem get4_tab4 {K : ℕ} (f : ℕ → ℕ → List ℚ) {b i : ℕ} (hb : b < 4) (hi : i < K) :
    get4 (tab4 K f) b i = f b i := by
  simp [get4, tab4, List.getD_eq_getElem?_getD, hb, hi]

/-- `qMat` computed with depth-1 shared tables (the form evaluated by `decide`). -/
def fastQ : List (List ℚ) :=
  let HV := tab4 S.K fun b j => hilbVec 7 (hh S D b j)
  let ER := tab4 S.K (er S D)
  let EV := tab4 S.K fun b j => hilbVec 32 (er S D b j)
  tabQ S.K fun i j => D.ds * ((List.range 4).map fun b =>
    (dotQ (D.WB b i) (get4 HV b j) + dotQ (D.WB b j) (get4 HV b i)) / 2 +
      dotQ (get4 ER b i) (get4 EV b j)).sum

theorem fastQ_eq {i j : ℕ} (hi : i < S.K) (hj : j < S.K) :
    matQ (fastQ S D) i j = matQ (qMat S D) i j := by
  simp only [fastQ, qMat, matQ_tabQ _ hi hj]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
  have hb' : b < 4 := List.mem_range.mp hb
  simp only [get4_tab4 _ hb' hi, get4_tab4 _ hb' hj, gramN]

/-- Lower bound `β_b` of the polynomial diagonal on `[0, 1]`. -/
def beta (b : ℕ) : ℚ :=
  S.c0 + (D.tayB b).base -
    qabsSum (qsub ((D.tayB b).poly S.rOrd (D.lowAff b).1 (D.lowAff b).2) (D.VtB b))

def branchOK (b : ℕ) : Bool :=
  let τ := D.tayB b
  let x0 := (D.lowAff b).1
  let x1 := (D.lowAff b).2
  τ.valid && decide (0 < τ.om) && decide (0 ≤ min x0 (x0 + x1)) &&
    decide (τ.t0 ≤ min x0 (x0 + x1) ^ 2) && qnonneg (qsub (τ.poly S.rOrd x0 x1) (D.VtB b))

def checkGeom : Bool :=
  decide (0 ≤ D.sa) && decide (0 < D.ds) && decide (D.sa + D.ds ≤ (1 - aHiQ) / 2) &&
    (List.range 4).all (fun b => branchOK S D b) &&
    pivots4Pos (beta S D 0) (beta S D 1) (beta S D 2) (beta S D 3) S.e2 S.e3 &&
    (List.range 4).all (fun b => (List.range S.K).all fun i => decide ((D.WB b i).length ≤ 7))

def checkLen : Bool :=
  (List.range 4).all fun b => (List.range S.K).all fun i => decide ((er S D b i).length ≤ 32)

/-- The certificate check of a four-branch subinterval. -/
def check : Bool :=
  checkGeom S D && checkLen S D && domCheck S.K (subMat S.K D.Qhat (fastQ S D)) &&
    (List.range S.K).all fun k => decide (pert S D k ≤ vecQ D.pertHat k)

end P4Sub

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
