import GaloisForLFunctions.HTGeometry.CoordinateInnerProductToolkit
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# Optimal qubit recovery with a ready branch

For the ready branch in Kanno and Soda (arXiv:2611.26368, §7.3), the lost
register carries one fixed label on input zero. The optimal entanglement
fidelity is half of one plus the norm of the input-one slice at that label.
The upper bound allows arbitrary finite recovery isometries. A controlled
projection with its orthogonal remainder implements an attaining isometry.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {F L K : Type*} [Fintype F] [Fintype L] [Fintype K]

/-- A deterministic recovery dilation. Tracing out its auxiliary output
gives the recovered logical qubit. -/
structure Recovery (F K : Type*) [Fintype F] [Fintype K] where
  apply : ((Bool × F) → ℂ) →ₗ[ℂ] ((Bool × K) → ℂ)
  norm_preserving : ∀ x, cnormSq (apply x) = cnormSq x

/-- A branch-preserving qubit encoding in which the zero branch has one
fixed label in the lost register. -/
structure Encoding (F L : Type*) [Fintype F] [Fintype L] where
  ready : L
  reference : F → ℂ
  signal : L → F → ℂ
  reference_norm : cnormSq reference = 1
  signal_norm : ∑ l, cnormSq (signal l) = 1

private def branch (b : Bool) (x : F → ℂ) : Bool × F → ℂ :=
  fun p => if p.1 = b then x p.2 else 0

/-- Amplitude of reading the correct output bit, as a vector of auxiliary labels. -/
def matching (R : Recovery F K) (b : Bool) (x : F → ℂ) : K → ℂ :=
  fun k => R.apply (branch b x) (b, k)

/-- Bell-state entanglement fidelity. The equal-bit Bell projection adds the
two matching branch amplitudes at each pair of lost and auxiliary labels. -/
def fidelity [DecidableEq L] (W : Encoding F L) (R : Recovery F K) : ℝ :=
  (∑ l, cnormSq (fun k =>
    (if l = W.ready then matching R false W.reference k else 0) +
      matching R true (W.signal l) k)) / 4

private theorem cnormSq_product {X : Type*} [Fintype X] (v : Bool × X → ℂ) :
    cnormSq v = cnormSq (fun x => v (false, x)) + cnormSq (fun x => v (true, x)) := by
  simp only [cnormSq, Fintype.sum_prod_type, Fintype.sum_bool]
  exact add_comm _ _

private theorem cnormSq_branch (b : Bool) (x : F → ℂ) : cnormSq (branch b x) = cnormSq x := by
  rw [cnormSq_product]
  cases b <;> simp [branch, cnormSq]

private theorem cnormSq_matching_le (R : Recovery F K) (b : Bool) (x : F → ℂ) :
    cnormSq (matching R b x) ≤ cnormSq x := by
  classical
  rw [← cnormSq_branch b x, ← R.norm_preserving, cnormSq_product]
  cases b
  · exact le_add_of_nonneg_right (cnormSq_nonneg _)
  · exact le_add_of_nonneg_left (cnormSq_nonneg _)

private theorem cnormSq_add (u v : K → ℂ) :
    cnormSq (fun k => u k + v k) = cnormSq u + cnormSq v + 2 * (cinner v u).re := by
  simp only [cnormSq, cinner, Complex.sq_norm, Complex.normSq_add,
    Finset.sum_add_distrib, Complex.re_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm (u k)]

private theorem re_cinner_le (u v : K → ℂ) :
    (cinner u v).re ≤ Real.sqrt (cnormSq u) * Real.sqrt (cnormSq v) := by
  calc
    _ ≤ ‖cinner u v‖ := Complex.re_le_norm _
    _ ≤ ∑ k, ‖u k‖ * ‖v k‖ := by
      unfold cinner
      exact (norm_sum_le _ _).trans (by simp only [norm_mul, Complex.norm_conj]; exact le_rfl)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

private theorem fidelity_expansion [DecidableEq L] (W : Encoding F L) (R : Recovery F K) :
    4 * fidelity W R = cnormSq (matching R false W.reference) +
      (∑ l, cnormSq (matching R true (W.signal l))) +
      2 * (cinner (matching R true (W.signal W.ready)) (matching R false W.reference)).re := by
  let a : K → ℂ := matching R false W.reference
  let b : L → K → ℂ := fun l => matching R true (W.signal l)
  let extra : L → ℝ := fun l => if l = W.ready then cnormSq a + 2 * (cinner (b l) a).re else 0
  have hterm (l : L) :
      cnormSq (fun k => (if l = W.ready then a k else 0) + b l k) = cnormSq (b l) + extra l := by
    by_cases h : l = W.ready
    · simp only [h, if_true, extra, cnormSq_add]
      ring
    · simp only [h, if_false, zero_add, extra, add_zero]
  have he : (∑ l, extra l) = cnormSq a + 2 * (cinner (b W.ready) a).re := by
    rw [Finset.sum_eq_single W.ready]
    · simp only [extra, if_true]
    · intro l _ hl
      simp only [extra, if_neg hl]
    · exact fun h => (h (Finset.mem_univ _)).elim
  unfold fidelity
  change 4 * ((∑ l, cnormSq (fun k => (if l = W.ready then a k else 0) + b l k)) / 4) = _
  simp only [hterm, Finset.sum_add_distrib, he]
  ring

/-- Every deterministic recovery keeps at most the surviving reference-slice
coherence in the Bell-state test. -/
theorem fidelity_le [DecidableEq L] (W : Encoding F L) (R : Recovery F K) :
    fidelity W R ≤ (1 + Real.sqrt (cnormSq (W.signal W.ready))) / 2 := by
  let a := matching R false W.reference
  let b := fun l => matching R true (W.signal l)
  have ha : cnormSq a ≤ 1 := (cnormSq_matching_le R false W.reference).trans_eq W.reference_norm
  have hb : (∑ l, cnormSq (b l)) ≤ 1 :=
    (Finset.sum_le_sum fun l _ => cnormSq_matching_le R true (W.signal l)).trans_eq W.signal_norm
  have hc : (cinner (b W.ready) a).re ≤ Real.sqrt (cnormSq (W.signal W.ready)) := by
    apply (re_cinner_le _ _).trans
    calc
      _ ≤ Real.sqrt (cnormSq (W.signal W.ready)) * Real.sqrt 1 :=
        mul_le_mul (Real.sqrt_le_sqrt (cnormSq_matching_le R true (W.signal W.ready)))
          (Real.sqrt_le_sqrt ha) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_one, mul_one]
  have h := fidelity_expansion W R
  change 4 * fidelity W R = cnormSq a + (∑ l, cnormSq (b l)) + 2 * (cinner (b W.ready) a).re at h
  linarith only [h, ha, hb, hc]

/-- Capture one direction coherently and keep its complementary vector in the
auxiliary output. This avoids any choice of a unitary completion. -/
private def capture (u x : F → ℂ) : Option F → ℂ
  | none => cinner u x
  | some i => x i - u i * cinner u x

private theorem capture_norm (u x : F → ℂ) (hu : cnormSq u = 1 ∨ u = 0) :
    cnormSq (capture u x) = cnormSq x := by
  rcases hu with hu | rfl
  · let z := cinner u x
    have hc : (∑ i, (x i * (starRingEnd ℂ) (u i * z)).re) = Complex.normSq z := by
      rw [← Complex.re_sum]
      have he : (∑ i, x i * (starRingEnd ℂ) (u i * z)) = z * (starRingEnd ℂ) z := by
        change (∑ i, x i * (starRingEnd ℂ) (u i * z)) = cinner u x * (starRingEnd ℂ) z
        rw [cinner, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
      rw [he]
      exact congrArg Complex.re (Complex.mul_conj z)
    unfold cnormSq
    rw [Fintype.sum_option]
    simp only [capture]
    change ‖z‖ ^ 2 + (∑ i, ‖x i - u i * z‖ ^ 2) = ∑ i, ‖x i‖ ^ 2
    simp only [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hc]
    rw [← show cnormSq u = ∑ i, Complex.normSq (u i) by simp only [cnormSq, Complex.sq_norm], hu]
    ring
  · simp only [cnormSq, Fintype.sum_option, capture, cinner, Pi.zero_apply,
      map_zero, zero_mul, Finset.sum_const_zero, sub_zero, norm_zero, zero_pow (Nat.succ_ne_zero 1),
      zero_add]

private def captureLinear (u : F → ℂ) : (F → ℂ) →ₗ[ℂ] (Option F → ℂ) where
  toFun := capture u
  map_add' x y := by
    have ha : cinner u (x + y) = cinner u x + cinner u y := by
      simp only [cinner, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    funext k
    cases k <;> simp only [capture, ha, Pi.add_apply]
    ring
  map_smul' c x := by
    have hm : cinner u (c • x) = c * cinner u x := by
      simp only [cinner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    funext k
    cases k
    · simp only [capture, hm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    · simp only [capture, hm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

private def captureDilation (u : Bool → F → ℂ) :
    ((Bool × F) → ℂ) →ₗ[ℂ] (Bool × Option F → ℂ) where
  toFun x p := captureLinear (u p.1) (fun f => x (p.1, f)) p.2
  map_add' x y := by
    funext p
    exact congrFun ((captureLinear (u p.1)).map_add (fun f => x (p.1,f))
      (fun f => y (p.1,f))) p.2
  map_smul' c x := by
    funext p
    exact congrFun ((captureLinear (u p.1)).map_smul c (fun f => x (p.1,f))) p.2

private theorem captureDilation_apply (u : Bool → F → ℂ)
    (x : Bool × F → ℂ) (b : Bool) (k : Option F) :
    captureDilation u x (b, k) = capture (u b) (fun f => x (b,f)) k := rfl

private theorem norm_captureDilation (u : Bool → F → ℂ)
    (hu : ∀ b, cnormSq (u b) = 1 ∨ u b = 0) (x : Bool × F → ℂ) :
    cnormSq (captureDilation u x) = cnormSq x := by
  rw [cnormSq_product (captureDilation u x), cnormSq_product x]
  simp only [captureDilation_apply, capture_norm _ _ (hu false), capture_norm _ _ (hu true)]

private def captureRecovery (u : Bool → F → ℂ)
    (hu : ∀ b, cnormSq (u b) = 1 ∨ u b = 0) : Recovery F (Option F) :=
  ⟨captureDilation u, norm_captureDilation u hu⟩

private theorem matching_captureRecovery (u : Bool → F → ℂ)
    (hu : ∀ b, cnormSq (u b) = 1 ∨ u b = 0) (b : Bool) (x : F → ℂ) :
    matching (captureRecovery u hu) b x = capture (u b) x := by
  have h : (fun f => branch b x (b, f)) = x := by funext f; simp only [branch, if_true]
  change capture (u b) (fun f => branch b x (b, f)) = _
  rw [h]

private def normalized (x : F → ℂ) : F → ℂ :=
  fun i => x i / (Real.sqrt (cnormSq x) : ℂ)

private theorem normalized_spec (x : F → ℂ) :
    (cnormSq (normalized x) = 1 ∨ normalized x = 0) ∧
      cinner (normalized x) x = (Real.sqrt (cnormSq x) : ℂ) := by
  classical
  let s := Real.sqrt (cnormSq x)
  have hs : s * s = cnormSq x := Real.mul_self_sqrt (cnormSq_nonneg x)
  by_cases h : cnormSq x = 0
  · have hs0 : s = 0 := by simp only [s, h, Real.sqrt_zero]
    have hn : normalized x = 0 := by
      funext i
      change x i / (s : ℂ) = 0
      rw [hs0, Complex.ofReal_zero, div_zero]
    refine ⟨Or.inr hn, ?_⟩
    rw [hn, ← show (s : ℂ) = (Real.sqrt (cnormSq x) : ℂ) from rfl, hs0]
    simp only [cinner, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, Complex.ofReal_zero]
  · have hpos : 0 < s := Real.sqrt_pos.mpr (lt_of_le_of_ne (cnormSq_nonneg x) (Ne.symm h))
    have hne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    constructor
    · left
      change (∑ i, ‖x i / (s : ℂ)‖ ^ 2) = 1
      simp only [Complex.sq_norm, Complex.normSq_div, Complex.normSq_ofReal, ← Finset.sum_div]
      rw [hs, show (∑ i, Complex.normSq (x i)) = cnormSq x by simp only [cnormSq, Complex.sq_norm]]
      exact div_self h
    · have he : cinner (normalized x) x = cinner x x / (s : ℂ) := by
        rw [cinner, cinner, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        change (starRingEnd ℂ) (x i / (s : ℂ)) * x i =
          ((starRingEnd ℂ) (x i) * x i) / (s : ℂ)
        rw [map_div₀, Complex.conj_ofReal]
        ring
      rw [he, cinner_self]
      change ((cnormSq x : ℝ) : ℂ) / (s : ℂ) = (s : ℂ)
      rw [← hs, Complex.ofReal_mul, mul_div_cancel_right₀ _ hne]

/-- The fidelity ceiling is reached by a finite recovery with one shared
auxiliary label and a register for the complementary amplitudes. -/
theorem exists_optimal_recovery [DecidableEq L] (W : Encoding F L) :
    ∃ R : Recovery F (Option F),
      fidelity W R = (1 + Real.sqrt (cnormSq (W.signal W.ready))) / 2 := by
  classical
  let u : Bool → F → ℂ
    | false => W.reference
    | true => normalized (W.signal W.ready)
  have hu : ∀ b, cnormSq (u b) = 1 ∨ u b = 0 := by
    intro b
    cases b
    · exact Or.inl W.reference_norm
    · exact (normalized_spec _).1
  let R := captureRecovery u hu
  refine ⟨R, ?_⟩
  have href : cinner W.reference W.reference = 1 := by
    rw [cinner_self, W.reference_norm, Complex.ofReal_one]
  have hcross :
      (cinner (capture (u true) (W.signal W.ready)) (capture (u false) W.reference)).re =
        Real.sqrt (cnormSq (W.signal W.ready)) := by
    unfold cinner
    rw [Fintype.sum_option]
    have hzero (i : F) : capture (u false) W.reference (some i) = 0 := by
      change W.reference i - W.reference i * cinner W.reference W.reference = 0
      rw [href, mul_one, sub_self]
    simp only [hzero, mul_zero, Finset.sum_const_zero, add_zero]
    dsimp only [capture]
    change ((starRingEnd ℂ) (cinner (normalized (W.signal W.ready)) (W.signal W.ready)) *
      cinner W.reference W.reference).re = _
    rw [(normalized_spec _).2, href, mul_one, Complex.conj_ofReal, Complex.ofReal_re]
  have h := fidelity_expansion W R
  simp only [R, matching_captureRecovery, capture_norm _ _ (hu _), W.reference_norm,
    W.signal_norm, hcross] at h
  linarith only [h]

#print axioms fidelity_le
#print axioms exists_optimal_recovery

end

end GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch
