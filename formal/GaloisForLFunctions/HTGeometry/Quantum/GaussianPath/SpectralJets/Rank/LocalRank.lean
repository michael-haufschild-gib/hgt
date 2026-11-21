import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.CoordinateCalculus
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # Full mixed-derivative rank on an analytic chart -/
open Set Metric Filter Topology Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
private abbrev P (n : ℕ) := Fin n → ℂ
variable {n k : ℕ}

/-- The signed maximal minors of a matrix with one more column than rows. -/
private def cof (G : Matrix (Fin k) (Fin (k+1)) ℂ) (j : Fin (k+1)) :=
  (-1:ℂ)^j.val * (G.submatrix id j.succAbove).det

private def prepend (G : Matrix (Fin k) (Fin (k+1)) ℂ) (v : Fin (k+1) → ℂ) :
    Matrix (Fin (k+1)) (Fin (k+1)) ℂ := Matrix.of (Fin.cons v G)

private theorem prepend_det (G : Matrix (Fin k) (Fin (k+1)) ℂ) (v : Fin (k+1) → ℂ) :
    (prepend G v).det = ∑ j, v j * cof G j := by
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  have he : (prepend G v).submatrix Fin.succ j.succAbove = G.submatrix id j.succAbove := by
    ext a b
    simp [prepend,Matrix.submatrix_apply]
  rw [he]
  simp [prepend,cof,mul_left_comm,mul_assoc]

private theorem cof_zero (G : Matrix (Fin k) (Fin (k+1)) ℂ) :
    cof G 0 = (G.submatrix id Fin.succ).det := by simp [cof]

private theorem analytic_cof {G : P n → Matrix (Fin k) (Fin (k+1)) ℂ} {y : P n}
    (h : ∀ a j, AnalyticAt ℂ (fun z => G z a j) y) (j : Fin (k+1)) :
    AnalyticAt ℂ (fun z => cof (G z) j) y :=
  analyticAt_const.mul (analyticAt_matrix_det_parametric (fun a b => h a (j.succAbove b)))

/-- No nonzero constant linear combination vanishes on a whole open
subchart. This condition is invariant under shrinking the observational chart. -/
def locallyIndependent (U : Set (P n)) (f : Fin k → P n → ℂ) : Prop :=
  ∀ V : Set (P n), V ⊆ U → IsOpen V → V.Nonempty → ∀ c : Fin k → ℂ,
    (∀ x ∈ V, ∑ j, f j x * c j = 0) → c = 0

private theorem independent_tail {U : Set (P n)} {f : Fin (k+1) → P n → ℂ}
    (h : locallyIndependent U f) : locallyIndependent U (fun j => f j.succ) := by
  intro V hv ho hn c hc
  have hzero := h V hv ho hn (Fin.cons 0 c) (fun x hx => by simpa [Fin.sum_univ_succ] using hc x hx)
  funext j
  exact congrFun hzero j.succ

/-- On every nonempty analytic chart with locally independent components,
some mixed derivatives of orders at most k−1 give a nonsingular k-row
matrix. The bound depends only on the number of components. -/
theorem exists_full_mixed_rank (k : ℕ) (f : Fin k → P n → ℂ) (U : Set (P n))
    (hU : IsOpen U) (hUne : U.Nonempty) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hfree : locallyIndependent U f) :
    ∃ x ∈ U, ∃ w : Fin k → List (Fin n), (∀ a, (w a).length ≤ k-1) ∧
      (Matrix.of fun a j => mixed (w a) (f j) x).det ≠ 0 := by
  induction k with
  | zero =>
    obtain ⟨x,hx⟩ := hUne
    exact ⟨x,hx,Fin.elim0,fun a => a.elim0,by simp⟩
  | succ k ih =>
    obtain ⟨x,hx,w,hw,hrank⟩ := ih (fun j => f j.succ) (fun j => hf j.succ) (independent_tail hfree)
    let G (z : P n) : Matrix (Fin k) (Fin (k+1)) ℂ := Matrix.of fun a j => mixed (w a) (f j) z
    let a (z : P n) := cof (G z)
    have hbase : a x 0 ≠ 0 := by simpa only [a,cof_zero,G,Matrix.submatrix,Matrix.of_apply,id_eq] using hrank
    have hana {z : P n} (hz : z ∈ U) (j : Fin (k+1)) : AnalyticAt ℂ (fun y => a y j) z :=
      analytic_cof (fun i l => mixed_analyticAt (hf l z hz) (w i)) j
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ a y 0 ≠ 0 :=
      Filter.inter_mem (hU.mem_nhds hx) ((hana hx 0).continuousAt.eventually_ne hbase)
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
    let V := ball x r
    have hsub : V ⊆ U := fun _ hz => (hball hz).1
    have hanz {z} (hz : z ∈ V) : a z 0 ≠ 0 := (hball hz).2
    have hxV : x ∈ V := mem_ball_self hr
    let c (z : P n) (j : Fin (k+1)) := a z j / a z 0
    have hca {z} (hz : z ∈ V) (j) : AnalyticAt ℂ (fun u => c u j) z :=
      (hana (hsub hz) j).div (hana (hsub hz) 0) (hanz hz)
    by_contra hno
    have hrel (v : List (Fin n)) (hv : v.length ≤ k) {z : P n} (hz : z ∈ V) :
        ∑ j, mixed v (f j) z * c z j = 0 := by
      have hdet : (prepend (G z) (fun j => mixed v (f j) z)).det = 0 := by
        by_contra hne
        refine hno ⟨z,hsub hz,Fin.cons v w,?_,?_⟩
        · refine Fin.cases (by simpa using hv) (fun i => ?_)
          simpa using (hw i).trans (Nat.sub_le _ _)
        · have hm : (Matrix.of fun i j => mixed ((Fin.cons v w : Fin (k+1) → List (Fin n)) i) (f j) z) =
                prepend (G z) (fun j => mixed v (f j) z) := by
            ext i j
            exact Fin.cases rfl (fun _ => rfl) i
          rwa [hm]
      rw [prepend_det] at hdet
      change ∑ j, mixed v (f j) z * (cof (G z) j / cof (G z) 0) = 0
      simp_rw [← mul_div_assoc,← Finset.sum_div,hdet,zero_div]
    -- Differentiate the pivot equations. Appending the coordinate derivative
    -- supplies the terms involving the changing rows, leaving G times dc = 0.
    have hder {z : P n} (hz : z ∈ V) (i : Fin n) :
        (fun j => fderiv ℂ (fun u => c u j) z (Pi.single i 1)) = 0 := by
      let b (j : Fin (k+1)) := fderiv ℂ (fun u => c u j) z (Pi.single i 1)
      have hcline (j) : HasDerivAt (fun t => c (coordLine z i t) j) (b j) 0 :=
        hasDerivAt_mixed_line (hca hz j).differentiableAt i
      have hlocal : ∀ᶠ t in 𝓝 0, coordLine z i t ∈ V :=
        coordLine_tendsto z i (isOpen_ball.mem_nhds hz)
      have hb0 : b 0 = 0 := (hcline 0).unique ((hasDerivAt_const 0 (1:ℂ)).congr_of_eventuallyEq
        (hlocal.mono fun t ht => div_self (hanz ht)))
      have hb (l : Fin k) : ∑ j, G z l j * b j = 0 := by
        have hlen := hw l
        have hpos := l.isLt
        have hnext := hrel (i::w l) (by simp only [List.length_cons]; omega) hz
        have hp := HasDerivAt.fun_sum (u := Finset.univ) fun (j : Fin (k+1)) _ =>
          (hasDerivAt_next_mixed (hf j z (hsub hz)) i (w l)).mul (hcline j)
        simp only [coordLine_zero] at hp
        have he := hp.unique ((hasDerivAt_const 0 (0:ℂ)).congr_of_eventuallyEq
          (hlocal.mono fun t ht => hrel (w l) (by omega) ht))
        rw [Finset.sum_add_distrib,hnext,zero_add] at he
        exact he
      let M := prepend (G z) (Pi.single 0 1)
      have hdet : M.det ≠ 0 := by simpa [M,prepend_det,Pi.single_apply] using hanz hz
      apply Matrix.eq_zero_of_mulVec_eq_zero hdet
      funext l
      refine Fin.cases ?_ (fun l => hb l) l
      change (∑ j, (Pi.single 0 (1:ℂ) : Fin (k+1) → ℂ) j * b j) = 0
      simpa [Pi.single_apply] using hb0
    have hconst {z : P n} (hz : z ∈ V) (j : Fin (k+1)) : c z j = c x j := by
      apply (convex_ball x r).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ)
        (fun y hy => (hca hy j).differentiableAt.differentiableWithinAt) _ hz hxV
      intro y hy
      rw [fderivWithin_of_isOpen isOpen_ball hy]
      exact fderiv_eq_zero_of_coordinate fun i => congrFun (hder hy i) j
    have he := hfree V hsub isOpen_ball ⟨x,hxV⟩ (c x) (by
      intro z hz
      simpa only [mixed,hconst hz] using hrel [] (Nat.zero_le _) hz)
    have hc0 : c x 0 = 0 := congrFun he 0
    simp [c,hbase] at hc0

#print axioms exists_full_mixed_rank
end
end GaloisForLFunctions.HTGeometry.SpectralJets
