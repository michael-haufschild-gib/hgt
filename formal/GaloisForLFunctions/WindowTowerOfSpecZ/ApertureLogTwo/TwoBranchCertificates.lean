import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.FourBranchSubintervalBound

/-!
# Two-branch subintervals and the endpoint slivers

On `u ∈ (1 - a, 1/2)` the folded form couples only `u` and `1 - u` through the prime-two contact
`e₂`. A certificate `P2Sub` on `u = ua + du ξ` has the same structure as `P4Sub` with two branches
and exact dual sources (no prime-three shift). `P2Sub.bound` is the analogue of `P4Sub.bound`.

The two endpoint slivers `(L₄ˡᵒ, (1 - a)/2)` and `(1 - a, u₂ʰⁱ)` carry no witness: constant
Taylor minorants keep the fiber coercive and the dual test is bounded by `sup`
(`sliver4_bound`, `sliver2_bound`).
-/

open Real MeasureTheory Set Finset intervalIntegral
open scoped BigOperators

namespace GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo

open SelectivePositivityAndThresholdLaws

/-- The two-branch fiber integrand. -/
noncomputable def f2Integrand (S : SectorData) (G : ℝ → ℝ) (m : Fin S.K → ℝ) (u : ℝ) : ℝ :=
  tridiag2Form (S.c0 + vTrue u) (S.c0 + vTrue (1 - u)) S.e2 (G u) (G (1 - u)) -
    2 * (G u * S.phiFn m u + G (1 - u) * S.phiFn m (1 - u))

theorem intervalIntegrable_f2Integrand {S : SectorData} {G : ℝ → ℝ} (hGc : Continuous G)
    (hiPot : IntegrableOn (fun u => G u ^ 2 * (S.c0 + vTrue u)) (Ioo (0 : ℝ) 1))
    (m : Fin S.K → ℝ) {α β : ℝ} (h0 : 0 ≤ α) (hαβ : α ≤ β) (h1 : β ≤ 1) :
    IntervalIntegrable (f2Integrand S G m) volume α β := by
  let H : ℝ → ℝ := fun u => (S.c0 + vTrue u) * G u ^ 2
  have hH : IntegrableOn H (Icc (0 : ℝ) 1) :=
    integrableOn_Icc_iff_integrableOn_Ioo.mpr (hiPot.congr_fun (fun u _ => mul_comm _ _)
      measurableSet_Ioo)
  have hii : ∀ p q : ℝ, 0 ≤ p → p ≤ q → q ≤ 1 → IntervalIntegrable H volume p q :=
    fun p q hp hpq hq => (intervalIntegrable_iff_integrableOn_Icc_of_le hpq).mpr
      (hH.mono_set (Icc_subset_Icc hp hq))
  have i0 : IntervalIntegrable H volume α β := hii α β h0 hαβ h1
  have i1 : IntervalIntegrable (fun u => H (1 - u)) volume α β := by
    have h := ((hii (1 - β) (1 - α) (by linarith) (by linarith) (by linarith)).comp_sub_left 1).symm
    simpa using h
  have hpc : Continuous (S.phiFn m) :=
    continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_qeval _)
  let R : ℝ → ℝ := fun u =>
    2 * S.e2 * G u * G (1 - u) - 2 * (G u * S.phiFn m u + G (1 - u) * S.phiFn m (1 - u))
  have hR : Continuous R := by dsimp only [R]; fun_prop
  have hf : f2Integrand S G m = fun u => (H u + H (1 - u)) + R u := by
    funext u; simp only [f2Integrand, tridiag2Form, H, R]; ring
  rw [hf]
  exact (i0.add i1).add (hR.intervalIntegrable α β)

/-- One two-branch subinterval `[ua, ua + du]` with its certificate. -/
structure P2Sub where
  ua : ℚ
  du : ℚ
  tay : List TaylorBranch
  Vt : List (List ℚ)
  W : List (List (List ℚ))
  Qhat : List (List ℚ)
  pertHat : List ℚ

namespace P2Sub

variable (S : SectorData) (D : P2Sub)

def tayB (b : ℕ) : TaylorBranch := D.tay.getD b ⟨0, 0, 0, 1, 0⟩
def VtB (b : ℕ) : List ℚ := D.Vt.getD b []
def WB (b i : ℕ) : List ℚ := (D.W.getD b []).getD i []

def lowAff : ℕ → ℚ × ℚ
  | 0 => (D.ua, D.du)
  | _ => (1 - D.ua, -D.du)

def vvExact : ℕ → ℕ → List ℚ
  | 0, k => qcomp (S.phiPoly k) [D.ua, D.du]
  | _, k => qcomp (S.phiPoly k) [1 - D.ua, -D.du]

def mwOf (w : ℕ → List ℚ) : ℕ → List ℚ
  | 0 => qadd (qmul (qadd [S.c0] (D.VtB 0)) (w 0)) (qsmul S.e2 (w 1))
  | _ => qadd (qsmul S.e2 (w 0)) (qmul (qadd [S.c0] (D.VtB 1)) (w 1))

def mw (b i : ℕ) : List ℚ := mwOf S D (fun b' => D.WB b' i) b
def vv (b k : ℕ) : List ℚ := P4Sub.roundList (vvExact S D b k)
def hh (b i : ℕ) : List ℚ :=
  qadd (qsub (qsmul 2 (vv S D b i)) (mw S D b i)) (qsmul pen (D.WB b i))
def er (b i : ℕ) : List ℚ := qsub (mw S D b i) (vv S D b i)
def eta (b k : ℕ) : ℚ := qabsSum (qsub (vvExact S D b k) (vv S D b k))

def qMat : List (List ℚ) :=
  tabQ S.K fun i j => D.du * ((List.range 2).map fun b =>
    (gramN 7 (D.WB b i) (hh S D b j) + gramN 7 (D.WB b j) (hh S D b i)) / 2 +
      gramN 32 (er S D b i) (er S D b j)).sum

def pert (k : ℕ) : ℚ :=
  D.du * (16 + 10 ^ 22) * S.K * ((List.range 2).map fun b => eta S D b k ^ 2).sum

/-- Table of `f b i` over `b < 2`, `i < K`. -/
def tab2 (K : ℕ) (f : ℕ → ℕ → List ℚ) : List (List (List ℚ)) :=
  (List.range 2).map fun b => (List.range K).map fun i => f b i

theorem get4_tab2 {K : ℕ} (f : ℕ → ℕ → List ℚ) {b i : ℕ} (hb : b < 2) (hi : i < K) :
    P4Sub.get4 (tab2 K f) b i = f b i := by
  simp [P4Sub.get4, tab2, List.getD_eq_getElem?_getD, hb, hi]

def fastEval : List (List ℚ) × List ℚ × Bool :=
  let VX := tab2 S.K fun b k => vvExact S D b k
  let VR := tab2 S.K fun b k => P4Sub.roundList (P4Sub.get4 VX b k)
  let MW := tab2 S.K fun b i => mw S D b i
  let HH := tab2 S.K fun b i =>
    qadd (qsub (qsmul 2 (P4Sub.get4 VR b i)) (P4Sub.get4 MW b i)) (qsmul pen (D.WB b i))
  let ER := tab2 S.K fun b i => qsub (P4Sub.get4 MW b i) (P4Sub.get4 VR b i)
  let HV := tab2 S.K fun b j => hilbVec 7 (P4Sub.get4 HH b j)
  let EV := tab2 S.K fun b j => hilbVec 32 (P4Sub.get4 ER b j)
  let Q := tabQ S.K fun i j => D.du * ((List.range 2).map fun b =>
    (dotQ (D.WB b i) (P4Sub.get4 HV b j) + dotQ (D.WB b j) (P4Sub.get4 HV b i)) / 2 +
      dotQ (P4Sub.get4 ER b i) (P4Sub.get4 EV b j)).sum
  let P := (List.range S.K).map fun k =>
    D.du * (16 + 10 ^ 22) * S.K * ((List.range 2).map fun b =>
      qabsSum (qsub (P4Sub.get4 VX b k) (P4Sub.get4 VR b k)) ^ 2).sum
  let L := (List.range 2).all fun b => (List.range S.K).all fun i =>
    decide ((P4Sub.get4 ER b i).length ≤ 32)
  (Q, P, L)

theorem fastEval_fst {i j : ℕ} (hi : i < S.K) (hj : j < S.K) :
    matQ (fastEval S D).1 i j = matQ (qMat S D) i j := by
  simp only [fastEval, qMat, matQ_tabQ _ hi hj]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
  have hb' : b < 2 := List.mem_range.mp hb
  simp only [get4_tab2 _ hb' hi, get4_tab2 _ hb' hj, gramN, vv, hh, er]

theorem fastEval_snd {k : ℕ} (hk : k < S.K) : vecQ (fastEval S D).2.1 k = pert S D k := by
  simp only [fastEval, pert, vecQ, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some]
  congr 2
  refine List.map_congr_left fun b hb => ?_
  rw [get4_tab2 _ (List.mem_range.mp hb) hk, get4_tab2 _ (List.mem_range.mp hb) hk, eta, vv]

theorem fastEval_lengths (h : (fastEval S D).2.2 = true) {b i : ℕ} (hb : b < 2) (hi : i < S.K) :
    (er S D b i).length ≤ 32 := by
  simp only [fastEval, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have := h b hb i hi
  simpa [get4_tab2 _ hb hi, er, vv] using this

def beta (b : ℕ) : ℚ :=
  S.c0 + (D.tayB b).base -
    qabsSum (qsub ((D.tayB b).poly S.rOrd (D.lowAff b).1 (D.lowAff b).2) (D.VtB b))

def branchOK (b : ℕ) : Bool :=
  let τ := D.tayB b
  let x0 := (D.lowAff b).1
  let x1 := (D.lowAff b).2
  τ.valid && decide (0 < τ.om) && decide (0 ≤ min x0 (x0 + x1)) &&
    decide (τ.t0 ≤ min x0 (x0 + x1) ^ 2) && qnonneg (qsub (τ.poly S.rOrd x0 x1) (D.VtB b))

def check : Bool :=
  decide (0 ≤ D.ua) && decide (0 < D.du) && decide (D.ua + D.du ≤ 1 / 2) &&
    (List.range 2).all (fun b => branchOK S D b) &&
    pivots2Pos (beta S D 0) (beta S D 1) S.e2 &&
    (List.range 2).all (fun b => (List.range S.K).all fun i => decide ((D.WB b i).length ≤ 7)) &&
    (fastEval S D).2.2 && domCheck S.K (subMat S.K D.Qhat (fastEval S D).1) &&
    (List.range S.K).all fun k => decide (vecQ (fastEval S D).2.1 k ≤ vecQ D.pertHat k)

end P2Sub

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
