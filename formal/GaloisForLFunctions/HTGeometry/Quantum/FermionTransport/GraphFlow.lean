import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.GraphCoercivity
import GaloisForLFunctions.HTGeometry.HodgeEdgeCochain.GlobalExistence
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.Activation
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Global finite Fermi–Dirac transport and relaxation

Clipping the particle and vacancy factors gives a bounded Lipschitz
extension of the Pauli-blocked current. Exponential barriers for the
positive parts of occupations and vacancies keep the forward solution
strictly inside the Pauli interval.
-/

open Set Filter
open scoped BigOperators NNReal

namespace GaloisForLFunctions.HTGeometry

section Autonomous

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A bounded Lipschitz autonomous field has an entire solution.
Uniqueness on overlapping time intervals makes the finite-horizon
solutions agree locally with the entire curve. -/
theorem exists_entire_autonomous_flow {F : X → X} {L K : ℝ≥0}
    (hL : ∀ x, ‖F x‖ ≤ L) (hK : LipschitzWith K F) (x₀ : X) :
    ∃ α : ℝ → X, α 0 = x₀ ∧ ∀ t : ℝ, HasDerivAt α (F (α t)) t := by
  have hex (n : ℕ) : ∃ α : ℝ → X, α 0 = x₀ ∧
      ∀ t ∈ Ioo (-(n : ℝ)) (n : ℝ), HasDerivAt α (F (α t)) t :=
    HodgeEdgeCochain.exists_solution_of_bounded_lipschitz hL hK x₀ ⟨n, Nat.cast_nonneg n⟩
  choose α h₀ hα using hex
  have hagree (m n : ℕ) (t : ℝ) (hm : |t| < (m : ℝ)) (hn : |t| < (n : ℝ)) : α m t = α n t := by
    let R := min (m : ℝ) (n : ℝ)
    have ht : |t| < R := lt_min hm hn
    have hR : 0 < R := (abs_nonneg t).trans_lt ht
    have hmem (s : ℝ) (hs : s ∈ Ioo (-R) R) : |s| < R := abs_lt.mpr hs
    have huniq : EqOn (α m) (α n) (Ioo (-R) R) :=
      ODE_solution_unique_of_mem_Ioo (v := fun _ => F) (s := fun _ => univ)
        (fun _ _ => hK.lipschitzOnWith) (show (0 : ℝ) ∈ Ioo (-R) R from ⟨neg_neg_of_pos hR, hR⟩)
        (fun _ hs => ⟨hα m _ (abs_lt.mp ((hmem _ hs).trans_le (min_le_left _ _))), mem_univ _⟩)
        (fun _ hs => ⟨hα n _ (abs_lt.mp ((hmem _ hs).trans_le (min_le_right _ _))), mem_univ _⟩)
        ((h₀ m).trans (h₀ n).symm)
    exact huniq (abs_lt.mp ht)
  let N (t : ℝ) := ⌊|t|⌋₊ + 1
  have hN (t : ℝ) : |t| < (N t : ℝ) := by
    change |t| < ((⌊|t|⌋₊ + 1 : ℕ) : ℝ)
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one |t|
  let x (t : ℝ) := α (N t) t
  refine ⟨x, h₀ (N 0), fun t => ?_⟩
  have ht := abs_lt.mp (hN t)
  have he : x =ᶠ[nhds t] α (N t) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hagree (N s) (N t) s (hN s) (abs_lt.mpr hs)
  exact he.hasDerivAt_iff.mpr (hα (N t) t ht)

end Autonomous

namespace Quantum.FermiGraph

noncomputable section

private theorem monotoneOn_exp_mul_of_positive_deriv {x dx : ℝ → ℝ} (c : ℝ)
    (hcont : ContinuousOn x (Ici 0))
    (hder : ∀ t : ℝ, 0 < t → HasDerivAt x (dx t) t)
    (hsign : ∀ t : ℝ, 0 < t → 0 ≤ dx t + c * x t) :
    MonotoneOn (fun t => Real.exp (c * t) * x t) (Ici 0) := by
  have hF (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun s => Real.exp (c * s) * x s) (Real.exp (c * t) * (dx t + c * x t)) t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (c * s)) (Real.exp (c * t) * c) t := by
      simpa only [id_eq, mul_one] using (((hasDerivAt_id t).const_mul c).exp)
    have ha := he.mul (hder t ht)
    rw [show Real.exp (c * t) * c * x t + Real.exp (c * t) * dx t =
      Real.exp (c * t) * (dx t + c * x t) by ring] at ha
    exact ha
  have hExp : Continuous (fun s : ℝ => Real.exp (c * s)) := by fun_prop
  have hpos (t : ℝ) (ht : t ∈ interior (Ici (0 : ℝ))) : 0 < t := by
    rwa [interior_Ici] at ht
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (hExp.continuousOn.mul hcont)
    (fun t ht => (hF t (hpos t ht)).differentiableAt.differentiableWithinAt) ?_
  intro t ht
  rw [(hF t (hpos t ht)).deriv]
  exact mul_nonneg (Real.exp_pos _).le (hsign t (hpos t ht))

private theorem monotoneOn_exp_mul {x dx : ℝ → ℝ} (c : ℝ)
    (hder : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (dx t) t)
    (hsign : ∀ t : ℝ, 0 ≤ t → 0 ≤ dx t + c * x t) :
    MonotoneOn (fun t => Real.exp (c * t) * x t) (Ici 0) :=
  monotoneOn_exp_mul_of_positive_deriv c
    (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    (fun t ht => hder t ht.le) (fun t ht => hsign t ht.le)

open HadamardLipschitz in
/-- A lower linear bound on the derivative in the nonnegative region
prevents a strictly positive coordinate from reaching zero. -/
theorem lower_exp_bound_of_inward_deriv {x dx : ℝ → ℝ} (a : ℝ)
    (hder : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (dx t) t)
    (hin : ∀ t : ℝ, 0 ≤ t → 0 ≤ x t → -a * x t ≤ dx t)
    (h₀ : 0 < x 0) {t : ℝ} (ht : 0 ≤ t) :
    x 0 * Real.exp (-(a * t)) ≤ x t := by
  let y (s : ℝ) := squaredRelu (x s)
  let dy (s : ℝ) := relu (x s) * dx s
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivAt y (dy s) s :=
    (hasDerivAt_squaredRelu (x s)).comp s (hder s hs)
  have hsign (s : ℝ) (hs : 0 ≤ s) : 0 ≤ dy s + (2 * a) * y s := by
    rcases le_total 0 (x s) with hx | hx
    · simp only [dy, y, squaredRelu, relu, max_eq_left hx]
      have hm := mul_nonneg hx (show 0 ≤ dx s + a * x s by linarith only [hin s hs hx])
      nlinarith only [hm]
    · simp only [dy, y, squaredRelu, relu, max_eq_right hx, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
        zero_div, mul_zero, add_zero, le_refl]
  have hmono := monotoneOn_exp_mul (2 * a) hd hsign
  have hE := hmono (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht
  simp only [mul_zero, Real.exp_zero, one_mul, y, squaredRelu, relu, max_eq_left h₀.le] at hE
  have hxt : 0 < x t := by
    by_contra! hn
    rw [max_eq_right hn, zero_pow (by norm_num : 2 ≠ 0), zero_div, mul_zero] at hE
    exact (not_le_of_gt (div_pos (pow_pos h₀ 2) (by norm_num))) hE
  rw [max_eq_left hxt.le] at hE
  have hexp : Real.exp ((2 * a) * t) = (Real.exp (a * t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : (x 0) ^ 2 ≤ (Real.exp (a * t) * x t) ^ 2 := by
    rw [mul_pow, ← hexp]
    linarith only [hE]
  have hle := (sq_le_sq₀ h₀.le (mul_nonneg (Real.exp_pos _).le hxt.le)).mp hsq
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hle)

open HadamardLipschitz in
private theorem nonneg_of_inward_deriv {x dx : ℝ → ℝ}
    (hder : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (dx t) t)
    (hin : ∀ t : ℝ, 0 ≤ t → x t ≤ 0 → 0 ≤ dx t)
    (h₀ : 0 ≤ x 0) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ x t := by
  let f (s : ℝ) := 0 - squaredRelu (0 - x s)
  let df (s : ℝ) := relu (0 - x s) * dx s
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivAt f (df s) s := by
    have h₁ := (hder s hs).const_sub 0
    have h₂ : HasDerivAt (fun z => squaredRelu (0 - x z)) (relu (0 - x s) * -dx s) s := by
      change HasDerivAt (squaredRelu ∘ fun z => 0 - x z) _ s
      exact (hasDerivAt_squaredRelu (0 - x s)).comp s h₁
    have h₃ := h₂.const_sub 0
    rw [mul_neg, neg_neg] at h₃
    exact h₃
  have hsign (s : ℝ) (hs : 0 ≤ s) : 0 ≤ df s + 0 * f s := by
    rcases le_total 0 (x s) with h | h
    · simp only [df, relu, max_eq_right (sub_nonpos.mpr h), zero_mul, add_zero, le_refl]
    · rw [zero_mul, add_zero]
      exact mul_nonneg (relu_nonneg _) (hin s hs h)
  have hm := monotoneOn_exp_mul 0 hd hsign (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht
  have hf₀ : f 0 = 0 := by
    unfold f squaredRelu relu
    rw [max_eq_right (sub_nonpos.mpr h₀)]
    norm_num
  simp only [zero_mul, Real.exp_zero, one_mul, hf₀] at hm
  by_contra! h
  have hsq : 0 < squaredRelu (0 - x t) := by
    unfold squaredRelu relu
    rw [max_eq_left (sub_nonneg.mpr h.le)]
    exact div_pos (pow_pos (sub_pos.mpr h) 2) (by norm_num)
  change 0 ≤ 0 - squaredRelu (0 - x t) at hm
  linarith only [hm, hsq]

private def occupationClip (x : ℝ) : ℝ := HodgeEdgeCochain.cutoff 0 (1 - x)

private theorem occupationClip_eq (x : ℝ) : occupationClip x = max (min x 1) 0 := by
  unfold occupationClip HodgeEdgeCochain.cutoff
  rw [show (0 : ℝ) + 1 - (1 - x) = x by ring]

private theorem occupationClip_nonneg (x : ℝ) : 0 ≤ occupationClip x :=
  HodgeEdgeCochain.cutoff_nonneg _ _

private theorem occupationClip_le_one (x : ℝ) : occupationClip x ≤ 1 :=
  HodgeEdgeCochain.cutoff_le_one _ _

private theorem occupationClip_le {x : ℝ} (hx : 0 ≤ x) : occupationClip x ≤ x := by
  rw [occupationClip_eq]
  exact max_le (min_le_left _ _) hx

private theorem le_occupationClip {x : ℝ} (hx : x ≤ 1) : x ≤ occupationClip x := by
  rw [occupationClip_eq, min_eq_left hx]
  exact le_max_left _ _

private theorem abs_occupationClip_sub_le (x y : ℝ) : |occupationClip x - occupationClip y| ≤ |x - y| := by
  unfold occupationClip
  have h := HodgeEdgeCochain.abs_cutoff_sub_le 0 (1 - x) (1 - y)
  rwa [show 1 - x - (1 - y) = -(x - y) by ring, abs_neg] at h

private def clippedTransfer (x y : ℝ) : ℝ := occupationClip x * (1 - occupationClip y)

private theorem clippedTransfer_nonneg (x y : ℝ) : 0 ≤ clippedTransfer x y :=
  mul_nonneg (occupationClip_nonneg x) (sub_nonneg.mpr (occupationClip_le_one y))

private theorem clippedTransfer_le_one (x y : ℝ) : clippedTransfer x y ≤ 1 :=
  (mul_le_of_le_one_right (occupationClip_nonneg x) (sub_le_self _ (occupationClip_nonneg y))).trans
    (occupationClip_le_one x)

private theorem abs_clippedTransfer_sub_le (x y z w : ℝ) :
    |clippedTransfer x y - clippedTransfer z w| ≤ |x - z| + |y - w| := by
  have he : clippedTransfer x y - clippedTransfer z w =
      (occupationClip x - occupationClip z) * (1 - occupationClip y) +
        occupationClip z * (occupationClip w - occupationClip y) := by
    unfold clippedTransfer
    ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr (occupationClip_le_one y)),
    abs_of_nonneg (occupationClip_nonneg z)]
  exact add_le_add
    ((mul_le_of_le_one_right (abs_nonneg _) (sub_le_self _ (occupationClip_nonneg y))).trans
      (abs_occupationClip_sub_le x z))
    ((mul_le_of_le_one_left (abs_nonneg _) (occupationClip_le_one z)).trans
      ((abs_occupationClip_sub_le w y).trans_eq (abs_sub_comm w y)))

variable {V : Type*} [Fintype V]

private def arrivalRate (G : WeightedGraph V) (E : V → ℝ) (v u : V) : ℝ :=
  G.w v u * Real.exp (E u)

omit [Fintype V] in
private theorem arrivalRate_nonneg (G : WeightedGraph V) (E : V → ℝ) (v u : V) :
    0 ≤ arrivalRate G E v u := mul_nonneg (G.w_nonneg v u) (Real.exp_pos _).le

private def clippedEdgeDrift (G : WeightedGraph V) (E x : V → ℝ) (v u : V) : ℝ :=
  arrivalRate G E v u * clippedTransfer (x u) (x v) -
    arrivalRate G E u v * clippedTransfer (x v) (x u)

/-- The bounded extension obtained by clipping particle and vacancy factors to the Pauli box. -/
def clippedDrift (G : WeightedGraph V) (E x : V → ℝ) (v : V) : ℝ :=
  ∑ u, clippedEdgeDrift G E x v u

/-- Sum of incoming and outgoing rate coefficients at a vertex. -/
def graphRateBound (G : WeightedGraph V) (E : V → ℝ) (v : V) : ℝ :=
  ∑ u, (arrivalRate G E v u + arrivalRate G E u v)

theorem graphRateBound_nonneg (G : WeightedGraph V) (E : V → ℝ) (v : V) :
    0 ≤ graphRateBound G E v :=
  Finset.sum_nonneg fun u _ => add_nonneg (arrivalRate_nonneg G E v u) (arrivalRate_nonneg G E u v)

/-- Clipping is inactive on the closed Pauli box, including at its boundary. -/
theorem clippedDrift_eq_of_box (G : WeightedGraph V) (E x : V → ℝ)
    (hx : ∀ v, x v ∈ Icc (0 : ℝ) 1) (v : V) :
    clippedDrift G E x v =
      ∑ u, (G.w v u * Real.exp (E u) * (x u * (1 - x v)) -
        G.w v u * Real.exp (E v) * (x v * (1 - x u))) := by
  rw [clippedDrift]
  apply Finset.sum_congr rfl
  intro u _
  have hp (w : V) : occupationClip (x w) = x w :=
    (occupationClip_le (hx w).1).antisymm (le_occupationClip (hx w).2)
  rw [clippedEdgeDrift, arrivalRate, arrivalRate, G.w_symm u v, clippedTransfer, clippedTransfer,
    hp u, hp v]

private theorem clippedDrift_eq_drift (G : WeightedGraph V) (E : V → ℝ) (p : V → Occupation) :
    clippedDrift G E (fun v => (p v : ℝ)) = drift G E p := by
  funext v
  rw [clippedDrift_eq_of_box G E _ (fun u => ⟨(p u).property.1.le, (p u).property.2.le⟩) v,
    drift, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [flux_eq_particle_hole]
  ring

omit [Fintype V] in
private theorem norm_clippedEdgeDrift_le (G : WeightedGraph V) (E x : V → ℝ) (v u : V) :
    ‖clippedEdgeDrift G E x v u‖ ≤ arrivalRate G E v u + arrivalRate G E u v := by
  rw [clippedEdgeDrift]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  simp only [Real.norm_eq_abs, abs_of_nonneg (arrivalRate_nonneg G E v u),
    abs_of_nonneg (arrivalRate_nonneg G E u v), abs_of_nonneg (clippedTransfer_nonneg (x u) (x v)),
    abs_of_nonneg (clippedTransfer_nonneg (x v) (x u))]
  exact add_le_add
    (mul_le_of_le_one_right (arrivalRate_nonneg G E v u) (clippedTransfer_le_one _ _))
    (mul_le_of_le_one_right (arrivalRate_nonneg G E u v) (clippedTransfer_le_one _ _))

private theorem norm_clippedEdgeDrift_sub_le (G : WeightedGraph V) (E x y : V → ℝ) (v u : V) :
    ‖clippedEdgeDrift G E x v u - clippedEdgeDrift G E y v u‖ ≤
      (arrivalRate G E v u + arrivalRate G E u v) * (2 * ‖x - y‖) := by
  have hcoord (i : V) : |x i - y i| ≤ ‖x - y‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
  have htransfer (i j : V) : ‖clippedTransfer (x i) (x j) - clippedTransfer (y i) (y j)‖ ≤
      2 * ‖x - y‖ := by
    rw [Real.norm_eq_abs]
    exact (abs_clippedTransfer_sub_le _ _ _ _).trans (by linarith only [hcoord i, hcoord j])
  have he : clippedEdgeDrift G E x v u - clippedEdgeDrift G E y v u =
      arrivalRate G E v u * (clippedTransfer (x u) (x v) - clippedTransfer (y u) (y v)) -
        arrivalRate G E u v * (clippedTransfer (x v) (x u) - clippedTransfer (y v) (y u)) := by
    unfold clippedEdgeDrift
    ring
  rw [he]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, add_mul]
  simp only [Real.norm_eq_abs (arrivalRate G E v u), Real.norm_eq_abs (arrivalRate G E u v),
    abs_of_nonneg (arrivalRate_nonneg G E v u), abs_of_nonneg (arrivalRate_nonneg G E u v)]
  exact add_le_add (mul_le_mul_of_nonneg_left (htransfer u v) (arrivalRate_nonneg G E v u))
    (mul_le_mul_of_nonneg_left (htransfer v u) (arrivalRate_nonneg G E u v))

private theorem clippedDrift_bounded_lipschitz (G : WeightedGraph V) (E : V → ℝ) :
    ∃ L K : ℝ≥0, (∀ x, ‖clippedDrift G E x‖ ≤ L) ∧ LipschitzWith K (clippedDrift G E) := by
  let C := ∑ v, graphRateBound G E v
  have hC : 0 ≤ C := Finset.sum_nonneg fun v _ => graphRateBound_nonneg G E v
  have hrow (v : V) : graphRateBound G E v ≤ C :=
    Finset.single_le_sum (fun w _ => graphRateBound_nonneg G E w) (Finset.mem_univ v)
  refine ⟨⟨C, hC⟩, ⟨2 * C, by positivity⟩, ?_, ?_⟩
  · intro x
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro v
    have hv : ‖clippedDrift G E x v‖ ≤ graphRateBound G E v := by
      unfold clippedDrift graphRateBound
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => norm_clippedEdgeDrift_le G E x v u)
    exact hv.trans (hrow v)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    change ‖clippedDrift G E x - clippedDrift G E y‖ ≤ (2 * C) * ‖x - y‖
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro v
    change ‖clippedDrift G E x v - clippedDrift G E y v‖ ≤ _
    calc
      _ ≤ graphRateBound G E v * (2 * ‖x - y‖) := by
        simp only [clippedDrift, graphRateBound, ← Finset.sum_sub_distrib, Finset.sum_mul]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => norm_clippedEdgeDrift_sub_le G E x y v u)
      _ ≤ C * (2 * ‖x - y‖) := mul_le_mul_of_nonneg_right (hrow v) (by positivity)
      _ = _ := by ring

private theorem clippedDrift_ge_lower (G : WeightedGraph V) (E x : V → ℝ) (v : V)
    (hx : 0 ≤ x v) : -graphRateBound G E v * x v ≤ clippedDrift G E x v := by
  unfold clippedDrift graphRateBound
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro u _
  have htransfer : clippedTransfer (x v) (x u) ≤ x v :=
    (mul_le_of_le_one_right (occupationClip_nonneg _)
      (sub_le_self _ (occupationClip_nonneg _))).trans (occupationClip_le hx)
  have hin := mul_nonneg (arrivalRate_nonneg G E v u) (clippedTransfer_nonneg (x u) (x v))
  have hout := mul_le_mul_of_nonneg_left htransfer (arrivalRate_nonneg G E u v)
  have hrate := mul_nonneg (arrivalRate_nonneg G E v u) hx
  unfold clippedEdgeDrift
  linarith only [hin, hout, hrate]

private theorem clippedDrift_le_upper (G : WeightedGraph V) (E x : V → ℝ) (v : V)
    (hx : x v ≤ 1) : clippedDrift G E x v ≤ graphRateBound G E v * (1 - x v) := by
  unfold clippedDrift graphRateBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro u _
  have htransfer : clippedTransfer (x u) (x v) ≤ 1 - x v :=
    (mul_le_of_le_one_left (sub_nonneg.mpr (occupationClip_le_one _))
      (occupationClip_le_one _)).trans (sub_le_sub_left (le_occupationClip hx) 1)
  have hin := mul_le_mul_of_nonneg_left htransfer (arrivalRate_nonneg G E v u)
  have hout := mul_nonneg (arrivalRate_nonneg G E u v) (clippedTransfer_nonneg (x v) (x u))
  have hrate := mul_nonneg (arrivalRate_nonneg G E u v) (sub_nonneg.mpr hx)
  unfold clippedEdgeDrift
  linarith only [hin, hout, hrate]

private theorem clippedDrift_nonneg_of_le_zero (G : WeightedGraph V) (E x : V → ℝ) (v : V)
    (hx : x v ≤ 0) : 0 ≤ clippedDrift G E x v := by
  have hc : occupationClip (x v) = 0 := by
    rw [occupationClip_eq, min_eq_left (hx.trans zero_le_one), max_eq_right hx]
  unfold clippedDrift
  apply Finset.sum_nonneg
  intro u _
  simp only [clippedEdgeDrift, clippedTransfer, hc, sub_zero, mul_one, zero_mul, mul_zero]
  exact mul_nonneg (arrivalRate_nonneg G E v u) (occupationClip_nonneg (x u))

private theorem clippedDrift_nonpos_of_one_le (G : WeightedGraph V) (E x : V → ℝ) (v : V)
    (hx : 1 ≤ x v) : clippedDrift G E x v ≤ 0 := by
  have hc : occupationClip (x v) = 1 := by
    rw [occupationClip_eq, min_eq_right hx, max_eq_left zero_le_one]
  unfold clippedDrift
  apply Finset.sum_nonpos
  intro u _
  simp only [clippedEdgeDrift, clippedTransfer, hc, sub_self, mul_zero, one_mul, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg (arrivalRate_nonneg G E u v)
    (sub_nonneg.mpr (occupationClip_le_one (x u))))

private theorem sum_clippedDrift_eq_zero (G : WeightedGraph V) (E x : V → ℝ) :
    ∑ v, clippedDrift G E x v = 0 := by
  have hswap : (∑ v, ∑ u, clippedEdgeDrift G E x v u) =
      -(∑ v, ∑ u, clippedEdgeDrift G E x v u) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by
      unfold clippedEdgeDrift
      ring
  unfold clippedDrift
  linarith only [hswap]

/-- A forward solution of the particle–hole equation on the closed Pauli box. -/
structure IsBoxOccupationFlow (G : WeightedGraph V) (E : V → ℝ) (x : ℝ → V → ℝ) : Prop where
  in_box : ∀ t : ℝ, 0 ≤ t → ∀ v : V, x t v ∈ Icc 0 1
  derivative : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (clippedDrift G E (x t)) t

/-- Every closed-box initial field has a global forward solution. At
a boundary face the particle or vacancy equation points inward. -/
theorem exists_global_box_occupation_flow (G : WeightedGraph V) (E x₀ : V → ℝ)
    (h₀ : ∀ v, x₀ v ∈ Icc (0 : ℝ) 1) :
    ∃ x : ℝ → V → ℝ, x 0 = x₀ ∧ IsBoxOccupationFlow G E x := by
  obtain ⟨L, K, hL, hK⟩ := clippedDrift_bounded_lipschitz G E
  obtain ⟨x, hx, hd⟩ := exists_entire_autonomous_flow hL hK x₀
  refine ⟨x, hx, ⟨?_, fun t _ => hd t⟩⟩
  intro t ht v
  have hv (s : ℝ) : HasDerivAt (fun z => x z v) (clippedDrift G E (x s) v) s :=
    (hasDerivAt_pi.mp (hd s)) v
  have hi : x 0 v = x₀ v := congrFun hx v
  constructor
  · exact nonneg_of_inward_deriv (fun s _ => hv s)
      (fun s _ hs => clippedDrift_nonneg_of_le_zero G E (x s) v hs)
      (by rw [hi]; exact (h₀ v).1) t ht
  · apply sub_nonneg.mp
    exact nonneg_of_inward_deriv (fun s _ => (hv s).const_sub 1)
      (fun s _ hs => neg_nonneg.mpr (clippedDrift_nonpos_of_one_le G E (x s) v (sub_nonpos.mp hs)))
      (by rw [hi]; exact sub_nonneg.mpr (h₀ v).2) t ht

variable {G : WeightedGraph V} {E : V → ℝ} {x y : ℝ → V → ℝ}

theorem IsBoxOccupationFlow.hasDerivAt_coordinate (h : IsBoxOccupationFlow G E x)
    (t : ℝ) (ht : 0 ≤ t) (v : V) :
    HasDerivAt (fun s => x s v) (clippedDrift G E (x t) v) t :=
  (hasDerivAt_pi.mp (h.derivative t ht)) v

/-- An exponential integrating factor makes each occupation nondecreasing. -/
theorem IsBoxOccupationFlow.occupation_exp_monotone (h : IsBoxOccupationFlow G E x) (v : V) :
    MonotoneOn (fun t => Real.exp (graphRateBound G E v * t) * x t v) (Ici 0) := by
  apply monotoneOn_exp_mul _ (fun t ht => h.hasDerivAt_coordinate t ht v)
  intro t ht
  have hlow := clippedDrift_ge_lower G E (x t) v (h.in_box t ht v).1
  linarith only [hlow]

/-- The same integrating factor makes each vacancy nondecreasing. -/
theorem IsBoxOccupationFlow.vacancy_exp_monotone (h : IsBoxOccupationFlow G E x) (v : V) :
    MonotoneOn (fun t => Real.exp (graphRateBound G E v * t) * (1 - x t v)) (Ici 0) := by
  apply monotoneOn_exp_mul _ (fun t ht => (h.hasDerivAt_coordinate t ht v).const_sub 1)
  intro t ht
  have hupp := clippedDrift_le_upper G E (x t) v (h.in_box t ht v).2
  linarith only [hupp]

/-- A forward solution takes values in the open occupation interval and
solves the original Pauli-blocked drift equation there. -/
structure IsOccupationFlow (G : WeightedGraph V) (E : V → ℝ) (x : ℝ → V → ℝ) : Prop where
  interior : ∀ t : ℝ, 0 ≤ t → ∀ v : V, x t v ∈ Ioo 0 1
  derivative : ∀ t : ℝ, ∀ ht : 0 ≤ t,
    HasDerivAt x (drift G E (fun v => ⟨x t v, interior t ht v⟩)) t

/-- Every interior field generates a global forward flow. Occupation
and vacancy each retain an explicit positive exponential lower bound. -/
theorem exists_global_occupation_flow (G : WeightedGraph V) (E : V → ℝ) (p₀ : V → Occupation) :
    ∃ x : ℝ → V → ℝ, x 0 = (fun v => (p₀ v : ℝ)) ∧ IsOccupationFlow G E x ∧
      ∀ t : ℝ, 0 ≤ t → ∀ v : V,
        (p₀ v : ℝ) * Real.exp (-(graphRateBound G E v * t)) ≤ x t v ∧
          (1 - (p₀ v : ℝ)) * Real.exp (-(graphRateBound G E v * t)) ≤ 1 - x t v := by
  obtain ⟨L, K, hL, hK⟩ := clippedDrift_bounded_lipschitz G E
  obtain ⟨x, h₀, hder⟩ := exists_entire_autonomous_flow hL hK (fun v => (p₀ v : ℝ))
  have hbound (t : ℝ) (ht : 0 ≤ t) (v : V) :
      (p₀ v : ℝ) * Real.exp (-(graphRateBound G E v * t)) ≤ x t v ∧
        (1 - (p₀ v : ℝ)) * Real.exp (-(graphRateBound G E v * t)) ≤ 1 - x t v := by
    have hcoord (s : ℝ) : HasDerivAt (fun z => x z v) (clippedDrift G E (x s) v) s :=
      (hasDerivAt_pi.mp (hder s)) v
    have hinit : x 0 v = (p₀ v : ℝ) := congrFun h₀ v
    constructor
    · have hpos : 0 < x 0 v := by rw [hinit]; exact (p₀ v).property.1
      have h := lower_exp_bound_of_inward_deriv (graphRateBound G E v)
        (fun s _ => hcoord s) (fun s _ hs => clippedDrift_ge_lower G E (x s) v hs) hpos ht
      rwa [hinit] at h
    · have hpos : 0 < 1 - x 0 v := by rw [hinit]; exact sub_pos.mpr (p₀ v).property.2
      have h := lower_exp_bound_of_inward_deriv (graphRateBound G E v)
        (fun s _ => (hcoord s).const_sub 1) (fun s _ hs =>
          by have hb := clippedDrift_le_upper G E (x s) v (sub_nonneg.mp hs)
             linarith only [hb]) hpos ht
      rwa [hinit] at h
  have hj (t : ℝ) (ht : 0 ≤ t) (v : V) : x t v ∈ Ioo 0 1 := by
    obtain ⟨hlo, hhi⟩ := hbound t ht v
    exact ⟨(mul_pos (p₀ v).property.1 (Real.exp_pos _)).trans_le hlo,
      sub_pos.mp ((mul_pos (sub_pos.mpr (p₀ v).property.2) (Real.exp_pos _)).trans_le hhi)⟩
  refine ⟨x, h₀, ⟨hj, ?_⟩, hbound⟩
  intro t ht
  have he : clippedDrift G E (x t) = drift G E (fun v => ⟨x t v, hj t ht v⟩) :=
    clippedDrift_eq_drift G E (fun v => ⟨x t v, hj t ht v⟩)
  simpa only [he] using hder t

/-- The state of a forward flow at a nonnegative time. -/
def IsOccupationFlow.atTime (h : IsOccupationFlow G E x) (t : ℝ) (ht : 0 ≤ t) (v : V) :
    Occupation := ⟨x t v, h.interior t ht v⟩

/-- Interior solutions also solve the equation on the closed box. -/
theorem IsOccupationFlow.toBox (h : IsOccupationFlow G E x) : IsBoxOccupationFlow G E x := by
  refine ⟨fun t ht v => ⟨(h.interior t ht v).1.le, (h.interior t ht v).2.le⟩, ?_⟩
  intro t ht
  have he : clippedDrift G E (x t) = drift G E (h.atTime t ht) :=
    clippedDrift_eq_drift G E (h.atTime t ht)
  rw [he]
  exact h.derivative t ht

/-- Two forward solutions with the same initial occupations agree at
every nonnegative time. -/
theorem IsBoxOccupationFlow.eqOn (hx : IsBoxOccupationFlow G E x) (hy : IsBoxOccupationFlow G E y)
    (h₀ : x 0 = y 0) : EqOn x y (Ici 0) := by
  obtain ⟨_, K, _, hK⟩ := clippedDrift_bounded_lipschitz G E
  intro t ht
  have hu : EqOn x y (Icc 0 t) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ => clippedDrift G E) (s := fun _ => univ)
      (fun _ _ => hK.lipschitzOnWith)
      (fun s hs => (hx.derivative s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hx.derivative s hs.1).hasDerivWithinAt) (fun _ _ => mem_univ _)
      (fun s hs => (hy.derivative s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hy.derivative s hs.1).hasDerivWithinAt) (fun _ _ => mem_univ _) h₀
  exact hu ⟨ht, le_rfl⟩

/-- Forward uniqueness for interior solutions. -/
theorem IsOccupationFlow.eqOn (hx : IsOccupationFlow G E x) (hy : IsOccupationFlow G E y)
    (h₀ : x 0 = y 0) : EqOn x y (Ici 0) :=
  hx.toBox.eqOn hy.toBox h₀

/-- The total occupation of a forward flow is constant. -/
theorem IsBoxOccupationFlow.mass_eq (h : IsBoxOccupationFlow G E x) {t : ℝ} (ht : 0 ≤ t) :
    (∑ v, x t v) = ∑ v, x 0 v := by
  let m (s : ℝ) : ℝ := ∑ v, x s v
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivAt m 0 s := by
    have hsum : HasDerivAt m (∑ v, clippedDrift G E (x s) v) s :=
      HasDerivAt.fun_sum (fun v _ => h.hasDerivAt_coordinate s hs v)
    rw [sum_clippedDrift_eq_zero] at hsum
    exact hsum
  have hp := monotoneOn_exp_mul (x := m) (dx := fun _ => 0) 0 hd (fun _ _ => by simp)
  have hdn (s : ℝ) (hs : 0 ≤ s) : HasDerivAt (fun z => 0 - m z) 0 s := by
    have hh := (hd s hs).const_sub 0
    rw [neg_zero] at hh
    exact hh
  have hn := monotoneOn_exp_mul (dx := fun _ => 0) 0 hdn (fun _ _ => by simp)
  have h₁ := hp (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht
  have h₂ := hn (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht
  simp only [zero_mul, Real.exp_zero, one_mul, zero_sub] at h₁ h₂
  exact (neg_le_neg_iff.mp h₂).antisymm h₁

/-- Mass conservation for interior solutions. -/
theorem IsOccupationFlow.mass_eq (h : IsOccupationFlow G E x) {t : ℝ} (ht : 0 ≤ t) :
    (∑ v, x t v) = ∑ v, x 0 v := h.toBox.mass_eq ht

private theorem hasDerivAt_freeEnergy_of_interior {t : ℝ}
    (p : V → Occupation) (hp : ∀ v, x t v = (p v : ℝ)) (hd : HasDerivAt x (drift G E p) t) :
    HasDerivAt (fun s => freeEnergy E (x s)) (-dissipation G E p) t := by
  have hcoord (v : V) : HasDerivAt (fun s => x s v) (drift G E p v) t :=
    (hasDerivAt_pi.mp hd) v
  rw [← sum_chemicalPotential_mul_drift G E p]
  unfold freeEnergy
  apply HasDerivAt.fun_sum
  intro v _
  have hbin : HasDerivAt (fun s => Real.binEntropy (x s v))
      ((Real.log (1 - (p v : ℝ)) - Real.log (p v : ℝ)) * drift G E p v) t := by
    have hb : HasDerivAt Real.binEntropy (Real.log (1 - (p v : ℝ)) - Real.log (p v : ℝ))
        (x t v) := by
      rw [hp v]
      exact Real.hasDerivAt_binEntropy (p v).property.1.ne' (p v).property.2.ne
    change HasDerivAt (Real.binEntropy ∘ fun s => x s v) _ t
    exact hb.comp t (hcoord v)
  have hh := ((hcoord v).const_mul (E v)).sub hbin
  have hv : 0 < 1 - (p v : ℝ) := sub_pos.mpr (p v).property.2
  have he : E v * drift G E p v -
      (Real.log (1 - (p v : ℝ)) - Real.log (p v : ℝ)) * drift G E p v =
        chemicalPotential E p v * drift G E p v := by
    rw [chemicalPotential, Real.log_div (p v).property.1.ne' hv.ne']
    ring
  rw [he] at hh
  exact hh

/-- Along the interior forward solution, free energy dissipates at the graph rate. -/
theorem IsOccupationFlow.hasDerivAt_freeEnergy (h : IsOccupationFlow G E x) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => freeEnergy E (x s)) (-dissipation G E (h.atTime t ht)) t :=
  hasDerivAt_freeEnergy_of_interior (h.atTime t ht) (fun _ => rfl) (h.derivative t ht)

private theorem continuous_freeEnergy (E : V → ℝ) : Continuous (freeEnergy E) := by
  unfold freeEnergy
  apply continuous_finsetSum _
  intro v _
  exact (continuous_const.mul (continuous_apply v)).sub
    (Real.binEntropy_continuous.comp (continuous_apply v))

/-- The dissipation bound integrates from time zero by continuity of
the free energy, even when the initial state is on the boundary. -/
theorem IsBoxOccupationFlow.exponential_relaxation_of_positive_interior
    (h : IsBoxOccupationFlow G E x) (root : V)
    (hpath : ∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) root v)
    (hm₀ : (∑ v, x 0 v) ∈ Ioo (0 : ℝ) (Fintype.card V : ℝ))
    (hi : ∀ t : ℝ, 0 < t → ∀ v : V, x t v ∈ Ioo 0 1) :
    ∃ μ k : ℝ, 0 < k ∧ gibbsMass E μ = (∑ v, x 0 v) ∧ ∀ t : ℝ, 0 ≤ t →
      let q (v : V) := (gibbsOccupation (E v) μ : ℝ)
      let M := Real.exp (-(k * t)) * (freeEnergy E (x 0) - freeEnergy E q)
      freeEnergy E (x t) - freeEnergy E q ≤ M ∧ 2 * ∑ v, (x t v - q v) ^ 2 ≤ M := by
  obtain ⟨μ, hμ, _⟩ := existsUnique_gibbsMass E hm₀
  obtain ⟨k, hk, hrate⟩ := exists_dissipation_ge_freeEnergy_gap G E μ root hpath
  let q (v : V) := (gibbsOccupation (E v) μ : ℝ)
  let e (t : ℝ) := freeEnergy E (x t) - freeEnergy E q
  let p (t : ℝ) (ht : 0 < t) (v : V) : Occupation := ⟨x t v, hi t ht v⟩
  let D (t : ℝ) := if ht : 0 < t then dissipation G E (p t ht) else 0
  have hmass (t : ℝ) (ht : 0 ≤ t) : (∑ v, x t v) = gibbsMass E μ :=
    (h.mass_eq ht).trans hμ.symm
  have hcont : ContinuousOn x (Ici 0) :=
    fun t ht => (h.derivative t ht).continuousAt.continuousWithinAt
  have he_cont : ContinuousOn e (Ici 0) :=
    ((continuous_freeEnergy E).comp_continuousOn hcont).sub continuousOn_const
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt (fun s => 0 - e s) (D t) t := by
    have he : clippedDrift G E (x t) = drift G E (p t ht) := clippedDrift_eq_drift G E (p t ht)
    have htime := h.derivative t ht.le
    rw [he] at htime
    have he' := hasDerivAt_freeEnergy_of_interior (p t ht) (fun _ => rfl) htime
    have hh := (he'.sub_const (freeEnergy E q)).const_sub 0
    rw [neg_neg] at hh
    dsimp only [D]
    rw [dif_pos ht]
    exact hh
  have hh (t : ℝ) (ht : 0 < t) : k * e t ≤ D t := by
    dsimp only [D]
    rw [dif_pos ht]
    exact hrate (p t ht) (hmass t ht.le)
  have hmono := monotoneOn_exp_mul_of_positive_deriv k (continuousOn_const.sub he_cont) hd
    (fun t ht => by
      change 0 ≤ D t + k * (0 - e t)
      linarith only [hh t ht])
  refine ⟨μ, k, hk, hμ, fun t ht => ?_⟩
  have het := hmono (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht
  simp only [mul_zero, Real.exp_zero, one_mul] at het
  change 0 - e 0 ≤ Real.exp (k * t) * (0 - e t) at het
  have hE : e t ≤ Real.exp (-(k * t)) * e 0 := by
    calc
      _ ≤ e 0 / Real.exp (k * t) := (le_div_iff₀ (Real.exp_pos _)).mpr (by linarith only [het])
      _ = _ := by rw [Real.exp_neg, div_eq_mul_inv, mul_comm]
  have hgap := freeEnergy_gibbs_gap E μ (h.in_box t ht) (hmass t ht)
  exact ⟨hE, hgap.trans hE⟩

/-- Every interior flow on a connected graph relaxes exponentially to
the Gibbs profile of its initial mass. -/
theorem IsOccupationFlow.exponential_relaxation (h : IsOccupationFlow G E x) (root : V)
    (hpath : ∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) root v) :
    ∃ μ k : ℝ, 0 < k ∧ gibbsMass E μ = (∑ v, x 0 v) ∧ ∀ t : ℝ, 0 ≤ t →
      let q (v : V) := (gibbsOccupation (E v) μ : ℝ)
      let M := Real.exp (-(k * t)) * (freeEnergy E (x 0) - freeEnergy E q)
      freeEnergy E (x t) - freeEnergy E q ≤ M ∧ 2 * ∑ v, (x t v - q v) ^ 2 ≤ M := by
  have hi (v : V) : x 0 v ∈ Ioo 0 1 := h.interior 0 le_rfl v
  have hm₀ : (∑ v, x 0 v) ∈ Ioo (0 : ℝ) (Fintype.card V : ℝ) := by
    constructor
    · have hsum := Finset.sum_lt_sum (s := Finset.univ) (f := fun _ : V => (0 : ℝ)) (g := x 0)
        (fun v _ => (hi v).1.le) ⟨root, Finset.mem_univ _, (hi root).1⟩
      simpa only [Finset.sum_const_zero] using hsum
    · have hsum := Finset.sum_lt_sum (s := Finset.univ) (f := x 0) (g := fun _ : V => (1 : ℝ))
        (fun v _ => (hi v).2.le) ⟨root, Finset.mem_univ _, (hi root).2⟩
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hsum
  exact h.toBox.exponential_relaxation_of_positive_interior root hpath hm₀
    (fun t ht => h.interior t ht.le)

#print axioms exists_entire_autonomous_flow
#print axioms lower_exp_bound_of_inward_deriv
#print axioms exists_global_box_occupation_flow
#print axioms IsBoxOccupationFlow.eqOn
#print axioms IsBoxOccupationFlow.mass_eq
#print axioms IsBoxOccupationFlow.exponential_relaxation_of_positive_interior
#print axioms exists_global_occupation_flow
#print axioms IsOccupationFlow.eqOn
#print axioms IsOccupationFlow.mass_eq
#print axioms IsOccupationFlow.hasDerivAt_freeEnergy
#print axioms IsOccupationFlow.exponential_relaxation

end

end Quantum.FermiGraph

end GaloisForLFunctions.HTGeometry
