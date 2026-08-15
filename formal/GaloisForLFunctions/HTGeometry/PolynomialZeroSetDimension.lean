import GaloisForLFunctions.HTGeometry.MvPolynomialSmoothEvaluation
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The Hausdorff dimension of a real polynomial zero set

A nonzero real polynomial in `n` variables has a zero set of Hausdorff dimension at most `n - 1`.

Away from its critical points the zero set is antilipschitz under the projection that forgets one
coordinate: between two zeros the mean value theorem produces an interior point where the gradient
is orthogonal to their difference, and a lower bound on one partial derivative together with an
upper bound on the others turns that into a bound on the corresponding coordinate difference.  The
critical part of the zero set lies in the zero set of a nonzero partial derivative, of strictly
smaller degree, so the bound follows by induction on the total degree.
-/

open MvPolynomial Set Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### A local-to-global bound for Hausdorff dimension -/

theorem dimH_le_of_locally {X : Type*} [EMetricSpace X] [SecondCountableTopology X]
    {s : Set X} {d : ENNReal} (h : ∀ x ∈ s, ∃ t, t ∈ nhdsWithin x s ∧ dimH t ≤ d) :
    dimH s ≤ d := by
  rw [← bsupr_limsup_dimH s]
  refine iSup₂_le fun x hx => ?_
  obtain ⟨t, ht, hdt⟩ := h x hx
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_smallSets_subset.2 ht] with u hu
  exact (dimH_mono hu).trans hdt

/-! ### Smoothness of polynomial evaluation on an arbitrary finite index -/

theorem contDiff_mvPolynomial_eval_pi {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℝ) :
    ContDiff ℝ ⊤ (fun x : ι → ℝ => MvPolynomial.eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (contDiff_const : ContDiff ℝ ⊤ (fun _ : ι → ℝ => c))
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P i hP => simpa using hP.mul (contDiff_apply ℝ ℝ i)

/-! ### The chain rule for a polynomial along a real curve -/

theorem hasDerivAt_mvPolynomial_eval_curve_real {ι : Type*} [Fintype ι] [DecidableEq ι] (P : MvPolynomial ι ℝ)
    (g : ι → ℝ → ℝ) (g' : ι → ℝ) (x : ℝ)
    (hg : ∀ j, HasDerivAt (g j) (g' j) x) :
    HasDerivAt (fun s => MvPolynomial.eval (fun j => g j s) P)
      (∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j P) * g' j) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hcf : (fun s => MvPolynomial.eval (fun j => g j s) (MvPolynomial.C a)) =
          fun _ => a := by
        funext s
        simp
      rw [hcf]
      simp only [MvPolynomial.pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
      exact hasDerivAt_const x a
  | add p q hp hq =>
      have hf : (fun s => MvPolynomial.eval (fun j => g j s) (p + q)) =
          fun s => MvPolynomial.eval (fun j => g j s) p +
            MvPolynomial.eval (fun j => g j s) q := by
        funext s
        simp
      rw [hf]
      convert! hp.add hq using 1
      simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
      have hfun : (fun s => MvPolynomial.eval (fun j => g j s) (p * MvPolynomial.X i)) =
          fun s => MvPolynomial.eval (fun j => g j s) p * g i s := by
        funext s
        simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [hfun]
      convert! hp.mul (hg i) using 1
      rw [Finset.sum_mul]
      have hterm : ∀ j : ι,
          MvPolynomial.eval (fun k => g k x) (MvPolynomial.pderiv j (p * MvPolynomial.X i))
              * g' j
            = MvPolynomial.eval (fun k => g k x) (MvPolynomial.pderiv j p) * g' j * g i x
              + (if j = i then MvPolynomial.eval (fun k => g k x) p * g' j else 0) := by
        intro j
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
        by_cases hji : j = i
        · subst hji
          simp only [Pi.single_eq_same, map_add, map_mul, MvPolynomial.eval_X, mul_one, if_true]
          ring
        · rw [if_neg hji]
          simp only [Pi.single_apply, if_neg (fun h : i = j => hji h.symm), map_mul,
            MvPolynomial.eval_X, mul_zero, add_zero]
          ring
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ i (fun j => MvPolynomial.eval (fun k => g k x) p * g' j),
        if_pos (Finset.mem_univ i)]

/-! ### Between two zeros the gradient is orthogonal to their difference -/

theorem exists_pderiv_inner_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (P : MvPolynomial ι ℝ)
    {s : Set (ι → ℝ)} (hs : Convex ℝ s) {x y : ι → ℝ} (hx : x ∈ s) (hy : y ∈ s)
    (hPx : MvPolynomial.eval x P = 0) (hPy : MvPolynomial.eval y P = 0) :
    ∃ ξ ∈ s, ∑ j, MvPolynomial.eval ξ (MvPolynomial.pderiv j P) * (x j - y j) = 0 := by
  classical
  set γ : ℝ → ι → ℝ := fun t j => y j + t * (x j - y j) with hγ
  have hmem : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ t ∈ s := by
    intro t ht
    have hcombo : γ t = (1 - t) • y + t • x := by
      funext j
      show y j + t * (x j - y j) = (1 - t) * y j + t * x j
      ring
    rw [hcombo]
    exact hs hy hx (by linarith [ht.1, ht.2]) ht.1 (by ring)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ => MvPolynomial.eval (γ u) P)
      (∑ j, MvPolynomial.eval (γ t) (MvPolynomial.pderiv j P) * (x j - y j)) t := by
    intro t
    exact hasDerivAt_mvPolynomial_eval_curve_real P (fun j u => y j + u * (x j - y j))
      (fun j => x j - y j) t (fun j => by
        simpa using ((hasDerivAt_id t).mul_const (x j - y j)).const_add (y j))
  have hzero : γ 0 = y := by funext j; simp [hγ]
  have hone : γ 1 = x := by funext j; show y j + 1 * (x j - y j) = x j; ring
  have hcont : Continuous fun u : ℝ => MvPolynomial.eval (γ u) P :=
    (contDiff_mvPolynomial_eval_pi P).continuous.comp (by
      refine continuous_pi fun j => ?_
      exact continuous_const.add (continuous_id.mul continuous_const))
  obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero (f := fun u : ℝ => MvPolynomial.eval (γ u) P)
    (a := 0) (b := 1) zero_lt_one hcont.continuousOn (by rw [hzero, hone, hPy, hPx])
  refine ⟨γ c, hmem c ⟨le_of_lt hc.1, le_of_lt hc.2⟩, ?_⟩
  rw [← (hderiv c).deriv]
  exact hc0

/-! ### Forgetting one coordinate is antilipschitz on a regular piece of the zero set -/

/-- The projection forgetting one coordinate. -/
def dropCoord {ι : Type*} [DecidableEq ι] (i : ι) (x : ι → ℝ) : {j : ι // j ≠ i} → ℝ := fun j => x j.1

theorem dist_dropCoord_le {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (x y : ι → ℝ)
    {j : ι} (hj : j ≠ i) : dist (x j) (y j) ≤ dist (dropCoord i x) (dropCoord i y) := by
  have := dist_le_pi_dist (dropCoord i x) (dropCoord i y) ⟨j, hj⟩
  exact this

theorem dist_le_of_zero_of_pderiv_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] (P : MvPolynomial ι ℝ) (i : ι)
    {s : Set (ι → ℝ)} (hs : Convex ℝ s) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hlow : ∀ z ∈ s, ε ≤ |MvPolynomial.eval z (MvPolynomial.pderiv i P)|)
    (hhigh : ∀ z ∈ s, ∀ j, |MvPolynomial.eval z (MvPolynomial.pderiv j P)| ≤ M)
    {x y : ι → ℝ} (hx : x ∈ s) (hy : y ∈ s)
    (hPx : MvPolynomial.eval x P = 0) (hPy : MvPolynomial.eval y P = 0) :
    dist x y ≤ (1 + M * Fintype.card ι / ε) * dist (dropCoord i x) (dropCoord i y) := by
  classical
  obtain ⟨ξ, hξ, hrel⟩ := exists_pderiv_inner_eq_zero P hs hx hy hPx hPy
  set d := dist (dropCoord i x) (dropCoord i y) with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hK1 : (1 : ℝ) ≤ 1 + M * Fintype.card ι / ε := by
    have : 0 ≤ M * Fintype.card ι / ε := by positivity
    linarith
  have hsplit : MvPolynomial.eval ξ (MvPolynomial.pderiv i P) * (x i - y i)
      = -∑ j ∈ Finset.univ.erase i,
        MvPolynomial.eval ξ (MvPolynomial.pderiv j P) * (x j - y j) := by
    have hsum := hrel
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)] at hsum
    linarith
  have hbound : |x i - y i| ≤ M * Fintype.card ι / ε * d := by
    have hεle : ε * |x i - y i|
        ≤ |MvPolynomial.eval ξ (MvPolynomial.pderiv i P)| * |x i - y i| :=
      mul_le_mul_of_nonneg_right (hlow ξ hξ) (abs_nonneg _)
    have hprod : |MvPolynomial.eval ξ (MvPolynomial.pderiv i P)| * |x i - y i|
        = |∑ j ∈ Finset.univ.erase i,
            MvPolynomial.eval ξ (MvPolynomial.pderiv j P) * (x j - y j)| := by
      rw [← abs_mul, hsplit, abs_neg]
    have hsum : |∑ j ∈ Finset.univ.erase i,
          MvPolynomial.eval ξ (MvPolynomial.pderiv j P) * (x j - y j)| ≤ M * Fintype.card ι * d := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ j ∈ Finset.univ.erase i,
          |MvPolynomial.eval ξ (MvPolynomial.pderiv j P) * (x j - y j)| ≤ M * d := by
        intro j hj
        rw [abs_mul]
        refine mul_le_mul (hhigh ξ hξ j) ?_ (abs_nonneg _) hM
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have := dist_dropCoord_le i x y hji
        rwa [Real.dist_eq] at this
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.univ.erase i).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
        have : (Finset.univ.erase i).card ≤ (Finset.univ : Finset ι).card :=
          Finset.card_le_card (Finset.erase_subset _ _)
        simp only [Finset.card_univ] at this
        exact_mod_cast this
      have hMd : 0 ≤ M * d := mul_nonneg hM hd0
      calc ((Finset.univ.erase i).card : ℝ) * (M * d) ≤ (Fintype.card ι : ℝ) * (M * d) :=
            mul_le_mul_of_nonneg_right hcard hMd
        _ = M * Fintype.card ι * d := by ring
    have hchain : ε * |x i - y i| ≤ M * Fintype.card ι * d := by
      rw [hprod] at hεle
      exact hεle.trans hsum
    rw [div_mul_eq_mul_div, le_div_iff₀ hε, mul_comm]
    linarith
  refine (dist_pi_le_iff (by positivity)).mpr fun j => ?_
  by_cases hji : j = i
  · subst hji
    rw [Real.dist_eq]
    calc |x j - y j| ≤ M * Fintype.card ι / ε * d := hbound
      _ ≤ (1 + M * Fintype.card ι / ε) * d := by
          refine mul_le_mul_of_nonneg_right (by linarith) hd0
  · calc dist (x j) (y j) ≤ d := dist_dropCoord_le i x y hji
      _ ≤ (1 + M * Fintype.card ι / ε) * d := by
          nlinarith [hd0, hK1]

/-! ### Degrees of partial derivatives -/

theorem totalDegree_pderiv_lt {ι : Type*} [Fintype ι] [DecidableEq ι] {P : MvPolynomial ι ℝ} (i : ι)
    (hP : 0 < P.totalDegree) : (MvPolynomial.pderiv i P).totalDegree < P.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree]
  refine lt_of_le_of_lt (Finset.sup_le fun m hm => ?_) (Nat.sub_lt hP zero_lt_one)
  have hne : MvPolynomial.coeff m (MvPolynomial.pderiv i P) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hne
  have hd : MvPolynomial.coeff (m + Finsupp.single i 1) P ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have hmem : m + Finsupp.single i 1 ∈ P.support := MvPolynomial.mem_support_iff.mpr hd
  have hle : (m + Finsupp.single i 1).sum (fun _ e => e) ≤ P.totalDegree :=
    MvPolynomial.le_totalDegree hmem
  have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  omega

theorem exists_pderiv_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {P : MvPolynomial ι ℝ} (hP : 0 < P.totalDegree) :
    ∃ i : ι, MvPolynomial.pderiv i P ≠ 0 := by
  classical
  obtain ⟨d, hd, hdeg⟩ : ∃ d ∈ P.support, 0 < d.sum fun _ e => e := by
    by_contra hcon
    push Not at hcon
    have : P.totalDegree ≤ 0 := Finset.sup_le fun d hd => by
      have := hcon d hd
      omega
    omega
  obtain ⟨i, hi⟩ : ∃ i, 0 < d i := by
    by_contra hcon
    push Not at hcon
    have hzero : d = 0 := by
      ext j
      have hj := hcon j
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [hzero] at hdeg
    simp at hdeg
  refine ⟨i, fun hzero => ?_⟩
  set m : ι →₀ ℕ := d - Finsupp.single i 1 with hm
  have hsplit : m + Finsupp.single i 1 = d := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp only [hm, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · simp only [hm, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply,
        if_neg (fun h : i = j => hji h.symm)]
      omega
  have hmi : ((m i : ℝ) + 1) = (d i : ℝ) := by
    have hnat : m i + 1 = d i := by
      simp only [hm, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hnat
  have hcoeff := MvPolynomial.coeff_pderiv (i := i) P m
  rw [hzero, MvPolynomial.coeff_zero, hsplit, hmi] at hcoeff
  have hdne : MvPolynomial.coeff d P ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hdi : ((d i : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_ne_zero hdne hdi) hcoeff.symm

/-! ### The dimension of the ambient hyperplane -/

theorem dimH_univ_dropCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    dimH (Set.univ : Set ({j : ι // j ≠ i} → ℝ)) = ((Fintype.card ι - 1 : ℕ) : ENNReal) := by
  classical
  rw [Real.dimH_univ_pi]
  congr 1
  have hc : Fintype.card {j : ι // ¬ (j = i)} = Fintype.card ι
      - Fintype.card {j : ι // j = i} := Fintype.card_subtype_compl _
  simp only [Fintype.card_subtype_eq] at hc
  exact hc

/-! ### The regular part of the zero set -/

set_option maxHeartbeats 1000000 in
theorem dimH_regular_zeroSet_le {ι : Type*} [Fintype ι] [DecidableEq ι] (P : MvPolynomial ι ℝ) (i : ι) :
    dimH {x : ι → ℝ | MvPolynomial.eval x P = 0 ∧
        MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0} ≤ ((Fintype.card ι - 1 : ℕ) : ENNReal) := by
  classical
  set S := {x : ι → ℝ | MvPolynomial.eval x P = 0 ∧
    MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0} with hS
  refine dimH_le_of_locally fun x₀ hx₀ => ?_
  set ε := |MvPolynomial.eval x₀ (MvPolynomial.pderiv i P)| / 2 with hε
  have hεpos : 0 < ε := by
    have := hx₀.2
    have habs : 0 < |MvPolynomial.eval x₀ (MvPolynomial.pderiv i P)| := abs_pos.mpr this
    positivity
  have hcont : Continuous fun z : ι → ℝ =>
      |MvPolynomial.eval z (MvPolynomial.pderiv i P)| :=
    (contDiff_mvPolynomial_eval_pi _).continuous.abs
  have hopen : IsOpen {z : ι → ℝ | ε < |MvPolynomial.eval z (MvPolynomial.pderiv i P)|} :=
    isOpen_lt continuous_const hcont
  have hx₀mem : x₀ ∈ {z : ι → ℝ | ε < |MvPolynomial.eval z (MvPolynomial.pderiv i P)|} := by
    show ε < _
    rw [hε]
    have habs : 0 < |MvPolynomial.eval x₀ (MvPolynomial.pderiv i P)| := abs_pos.mpr hx₀.2
    linarith
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp hopen x₀ hx₀mem
  obtain ⟨M, hMbound⟩ := (isCompact_closedBall x₀ (ρ/2)).exists_bound_of_continuousOn
    (f := fun z : ι → ℝ => ∑ j, |MvPolynomial.eval z (MvPolynomial.pderiv j P)|)
    (Continuous.continuousOn (continuous_finsetSum _ fun j _ =>
      (contDiff_mvPolynomial_eval_pi _).continuous.abs))
  have hM0 : 0 ≤ M := by
    have hx : x₀ ∈ Metric.closedBall x₀ (ρ/2) := Metric.mem_closedBall_self (by linarith)
    have := hMbound x₀ hx
    refine le_trans ?_ this
    positivity
  set B := Metric.ball x₀ (ρ/2) with hB
  have hBsub : B ⊆ Metric.closedBall x₀ (ρ/2) := Metric.ball_subset_closedBall
  have hBsub2 : B ⊆ Metric.ball x₀ ρ := Metric.ball_subset_ball (by linarith)
  have hlow : ∀ z ∈ B, ε ≤ |MvPolynomial.eval z (MvPolynomial.pderiv i P)| :=
    fun z hz => le_of_lt (hsub (hBsub2 hz))
  have hhigh : ∀ z ∈ B, ∀ j, |MvPolynomial.eval z (MvPolynomial.pderiv j P)| ≤ M := by
    intro z hz j
    refine le_trans ?_ (hMbound z (hBsub hz))
    refine le_trans (Finset.single_le_sum (f := fun j =>
      |MvPolynomial.eval z (MvPolynomial.pderiv j P)|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ j)) ?_
    exact le_abs_self _
  refine ⟨S ∩ B, inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ (by linarith)), ?_⟩
  set K : NNReal := Real.toNNReal (1 + M * Fintype.card ι / ε) with hK
  have hKval : (K : ℝ) = 1 + M * Fintype.card ι / ε := by
    rw [hK, Real.coe_toNNReal]
    positivity
  have hanti : AntilipschitzWith K
      (fun z : ↥(S ∩ B) => dropCoord i (z : ι → ℝ)) := by
    refine AntilipschitzWith.of_le_mul_dist fun z w => ?_
    rw [hKval]
    exact dist_le_of_zero_of_pderiv_bounds P i (convex_ball x₀ (ρ/2)) hεpos hM0
      (fun u hu => hlow u hu) (fun u hu j => hhigh u hu j)
      z.2.2 w.2.2 z.2.1.1 w.2.1.1
  have h1 : dimH (Set.univ : Set ↥(S ∩ B))
      ≤ dimH ((fun z : ↥(S ∩ B) => dropCoord i (z : ι → ℝ)) '' Set.univ) :=
    hanti.le_dimH_image Set.univ
  have h2 : dimH (Set.univ : Set ↥(S ∩ B)) = dimH (S ∩ B) := by
    have := Isometry.dimH_image (isometry_subtype_coe (s := S ∩ B)) (Set.univ)
    rw [Subtype.coe_image_univ] at this
    exact this.symm
  have h3 : dimH ((fun z : ↥(S ∩ B) => dropCoord i (z : ι → ℝ)) '' Set.univ)
      ≤ ((Fintype.card ι - 1 : ℕ) : ENNReal) := by
    refine le_trans (dimH_mono (Set.subset_univ _)) ?_
    exact le_of_eq (dimH_univ_dropCoord i)
  rw [← h2]
  exact h1.trans h3

/-! ### The Hausdorff dimension of a polynomial zero set -/

/-- **A nonzero real polynomial has a zero set of Hausdorff dimension at most `n - 1`.** -/
theorem dimH_zeroSet_le {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (k : ℕ) (P : MvPolynomial ι ℝ), P.totalDegree ≤ k → P ≠ 0 →
      dimH {x : ι → ℝ | MvPolynomial.eval x P = 0} ≤ ((Fintype.card ι - 1 : ℕ) : ENNReal) := by
  classical
  intro k
  induction k with
  | zero =>
      intro P hdeg hP
      set a := P.coeff 0 with ha0
      have hC : P = MvPolynomial.C a :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hdeg)
      have ha : a ≠ 0 := fun h => hP (by rw [hC, h, map_zero])
      have hempty : {x : ι → ℝ | MvPolynomial.eval x P = 0} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hC,
          MvPolynomial.eval_C]
        exact ha
      rw [hempty, dimH_empty]
      simp
  | succ k ih =>
      intro P hdeg hP
      by_cases hzero : P.totalDegree = 0
      · set a := P.coeff 0 with ha0
        have hC : P = MvPolynomial.C a :=
          MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
        have ha : a ≠ 0 := fun h => hP (by rw [hC, h, map_zero])
        have hempty : {x : ι → ℝ | MvPolynomial.eval x P = 0} = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hC,
            MvPolynomial.eval_C]
          exact ha
        rw [hempty, dimH_empty]
        simp
      · have hpos : 0 < P.totalDegree := Nat.pos_of_ne_zero hzero
        obtain ⟨i, hi⟩ := exists_pderiv_ne_zero hpos
        have hsplit : {x : ι → ℝ | MvPolynomial.eval x P = 0}
            ⊆ {x : ι → ℝ | MvPolynomial.eval x P = 0 ∧
                MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0}
              ∪ {x : ι → ℝ | MvPolynomial.eval x (MvPolynomial.pderiv i P) = 0} := by
          intro x hx
          by_cases hd : MvPolynomial.eval x (MvPolynomial.pderiv i P) = 0
          · exact Or.inr hd
          · exact Or.inl ⟨hx, hd⟩
        refine le_trans (dimH_mono hsplit) ?_
        rw [dimH_union]
        refine max_le (dimH_regular_zeroSet_le P i) ?_
        exact ih (MvPolynomial.pderiv i P)
          (by have := totalDegree_pderiv_lt i hpos; omega) hi

/-- **The zero set of a nonzero real polynomial has Hausdorff dimension at most `n - 1`.** -/
theorem dimH_setOf_eval_eq_zero_le {ι : Type*} [Fintype ι] [DecidableEq ι] (P : MvPolynomial ι ℝ) (hP : P ≠ 0) :
    dimH {x : ι → ℝ | MvPolynomial.eval x P = 0} ≤ ((Fintype.card ι - 1 : ℕ) : ENNReal) :=
  dimH_zeroSet_le P.totalDegree P le_rfl hP

/-! ### Complex polynomial zero sets -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The coefficientwise real part of a polynomial with complex coefficients. -/
def rePoly (Q : MvPolynomial κ ℂ) : MvPolynomial κ ℝ :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm
    (Finsupp.mapRange Complex.re Complex.zero_re (AddMonoidAlgebra.coeff Q))

/-- The coefficientwise imaginary part of a polynomial with complex coefficients. -/
def imPoly (Q : MvPolynomial κ ℂ) : MvPolynomial κ ℝ :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm
    (Finsupp.mapRange Complex.im Complex.zero_im (AddMonoidAlgebra.coeff Q))

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem coeff_rePoly (Q : MvPolynomial κ ℂ) (d : κ →₀ ℕ) :
    MvPolynomial.coeff d (rePoly Q) = (MvPolynomial.coeff d Q).re := rfl

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem coeff_imPoly (Q : MvPolynomial κ ℂ) (d : κ →₀ ℕ) :
    MvPolynomial.coeff d (imPoly Q) = (MvPolynomial.coeff d Q).im := rfl

omit [Fintype κ] [DecidableEq κ] in
theorem support_rePoly_subset (Q : MvPolynomial κ ℂ) : (rePoly Q).support ⊆ Q.support := by
  intro d hd
  rw [MvPolynomial.mem_support_iff] at hd ⊢
  intro hzero
  exact hd (by rw [coeff_rePoly, hzero, Complex.zero_re])

omit [Fintype κ] [DecidableEq κ] in
theorem support_imPoly_subset (Q : MvPolynomial κ ℂ) : (imPoly Q).support ⊆ Q.support := by
  intro d hd
  rw [MvPolynomial.mem_support_iff] at hd ⊢
  intro hzero
  exact hd (by rw [coeff_imPoly, hzero, Complex.zero_im])

omit [DecidableEq κ] in
theorem eval_rePoly (Q : MvPolynomial κ ℂ) (u : κ → ℝ) :
    MvPolynomial.eval u (rePoly Q) = (MvPolynomial.eval (fun v => (u v : ℂ)) Q).re := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Complex.re_sum,
    Finset.sum_subset (f := fun d => MvPolynomial.coeff d (rePoly Q) * ∏ i, u i ^ d i)
      (support_rePoly_subset Q) (fun d _ hd => by
        rw [MvPolynomial.notMem_support_iff.mp hd, zero_mul])]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hprod : (∏ i, (u i : ℂ) ^ d i) = ((∏ i, u i ^ d i : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hprod, coeff_rePoly, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

omit [DecidableEq κ] in
theorem eval_imPoly (Q : MvPolynomial κ ℂ) (u : κ → ℝ) :
    MvPolynomial.eval u (imPoly Q) = (MvPolynomial.eval (fun v => (u v : ℂ)) Q).im := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Complex.im_sum,
    Finset.sum_subset (f := fun d => MvPolynomial.coeff d (imPoly Q) * ∏ i, u i ^ d i)
      (support_imPoly_subset Q) (fun d _ hd => by
        rw [MvPolynomial.notMem_support_iff.mp hd, zero_mul])]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hprod : (∏ i, (u i : ℂ) ^ d i) = ((∏ i, u i ^ d i : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hprod, coeff_imPoly, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add]

omit [Fintype κ] [DecidableEq κ] in
theorem rePoly_ne_zero_or_imPoly_ne_zero {Q : MvPolynomial κ ℂ} (hQ : Q ≠ 0) :
    rePoly Q ≠ 0 ∨ imPoly Q ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  refine hQ (MvPolynomial.ext _ _ fun d => ?_)
  have hre : (MvPolynomial.coeff d Q).re = 0 := by
    rw [← coeff_rePoly, hcon.1, MvPolynomial.coeff_zero]
  have him : (MvPolynomial.coeff d Q).im = 0 := by
    rw [← coeff_imPoly, hcon.2, MvPolynomial.coeff_zero]
  rw [MvPolynomial.coeff_zero]
  exact Complex.ext hre him

/-- Reading a real point of the doubled index set as a complex point. -/
def realifyPoint (u : (κ ⊕ κ) → ℝ) : κ → ℂ := fun j => ⟨u (Sum.inl j), u (Sum.inr j)⟩

omit [DecidableEq κ] in
theorem lipschitzWith_realifyPoint : LipschitzWith 2 (realifyPoint (κ := κ)) := by
  refine LipschitzWith.of_dist_le_mul fun u u' => ?_
  refine (dist_pi_le_iff (by positivity)).mpr fun j => ?_
  have hre : |u (Sum.inl j) - u' (Sum.inl j)| ≤ dist u u' := by
    have := dist_le_pi_dist u u' (Sum.inl j)
    rwa [Real.dist_eq] at this
  have him : |u (Sum.inr j) - u' (Sum.inr j)| ≤ dist u u' := by
    have := dist_le_pi_dist u u' (Sum.inr j)
    rwa [Real.dist_eq] at this
  have hbound : ‖realifyPoint u j - realifyPoint u' j‖
      ≤ |u (Sum.inl j) - u' (Sum.inl j)| + |u (Sum.inr j) - u' (Sum.inr j)| := by
    have hsub : realifyPoint u j - realifyPoint u' j
        = ⟨u (Sum.inl j) - u' (Sum.inl j), u (Sum.inr j) - u' (Sum.inr j)⟩ := rfl
    rw [hsub]
    exact Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.dist_eq]
  calc ‖realifyPoint u j - realifyPoint u' j‖ ≤ _ := hbound
    _ ≤ dist u u' + dist u u' := add_le_add hre him
    _ = 2 * dist u u' := by ring
    _ = ((2 : NNReal) : ℝ) * dist u u' := by norm_num

/-- The substitution `x_j ↦ x_{inl j} + i x_{inr j}`. -/
def complexSplitSubst : MvPolynomial κ ℂ →ₐ[ℂ] MvPolynomial (κ ⊕ κ) ℂ :=
  MvPolynomial.aeval fun j => MvPolynomial.X (Sum.inl j)
    + MvPolynomial.C Complex.I * MvPolynomial.X (Sum.inr j)

omit [Fintype κ] [DecidableEq κ] in
theorem complexSplitSubst_ne_zero {Q : MvPolynomial κ ℂ} (hQ : Q ≠ 0) :
    complexSplitSubst Q ≠ 0 := by
  intro hzero
  refine hQ ?_
  have hret : (MvPolynomial.aeval (Sum.elim (MvPolynomial.X : κ → MvPolynomial κ ℂ)
      (fun _ => 0))).comp (complexSplitSubst (κ := κ)) = AlgHom.id ℂ (MvPolynomial κ ℂ) := by
    apply MvPolynomial.algHom_ext
    intro j
    show MvPolynomial.aeval (Sum.elim (MvPolynomial.X : κ → MvPolynomial κ ℂ) (fun _ => 0))
      (complexSplitSubst (MvPolynomial.X j)) = MvPolynomial.X j
    rw [complexSplitSubst, MvPolynomial.aeval_X]
    simp
  have := congrArg (fun f : MvPolynomial κ ℂ →ₐ[ℂ] MvPolynomial κ ℂ => f Q) hret
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq] at this
  rw [hzero, map_zero] at this
  exact this.symm

omit [Fintype κ] [DecidableEq κ] in
theorem eval_complexSplitSubst (Q : MvPolynomial κ ℂ) (u : (κ ⊕ κ) → ℝ) :
    MvPolynomial.eval (fun v => (u v : ℂ)) (complexSplitSubst Q)
      = MvPolynomial.eval (realifyPoint u) Q := by
  have hbind : complexSplitSubst Q = MvPolynomial.bind₁
      (fun j => MvPolynomial.X (Sum.inl j)
        + MvPolynomial.C Complex.I * MvPolynomial.X (Sum.inr j)) Q := rfl
  rw [hbind]
  show MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun v => (u v : ℂ)) _ = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  show MvPolynomial.eval (fun j => MvPolynomial.eval (fun v => (u v : ℂ))
    (MvPolynomial.X (Sum.inl j) + MvPolynomial.C Complex.I * MvPolynomial.X (Sum.inr j))) Q
    = MvPolynomial.eval (realifyPoint u) Q
  have hpt : (fun j => MvPolynomial.eval (fun v => (u v : ℂ))
      (MvPolynomial.X (Sum.inl j) + MvPolynomial.C Complex.I * MvPolynomial.X (Sum.inr j)))
      = realifyPoint u := by
    funext j
    show MvPolynomial.eval (fun v => (u v : ℂ))
        (MvPolynomial.X (Sum.inl j) + MvPolynomial.C Complex.I * MvPolynomial.X (Sum.inr j))
      = realifyPoint u j
    rw [map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X, MvPolynomial.eval_C]
    apply Complex.ext <;> simp [realifyPoint]
  rw [hpt]

/-- **A nonzero complex polynomial has a zero set of Hausdorff dimension at most
`2 · card κ - 1`.** -/
theorem dimH_setOf_complex_eval_eq_zero_le (Q : MvPolynomial κ ℂ) (hQ : Q ≠ 0) :
    dimH {z : κ → ℂ | MvPolynomial.eval z Q = 0}
      ≤ ((2 * Fintype.card κ - 1 : ℕ) : ENNReal) := by
  classical
  set Q' := complexSplitSubst Q with hQ'
  have hQ'ne : Q' ≠ 0 := complexSplitSubst_ne_zero hQ
  obtain hP | hP := rePoly_ne_zero_or_imPoly_ne_zero hQ'ne
  · refine le_trans (dimH_mono (?_ : {z : κ → ℂ | MvPolynomial.eval z Q = 0}
      ⊆ realifyPoint '' {u : (κ ⊕ κ) → ℝ | MvPolynomial.eval u (rePoly Q') = 0})) ?_
    · intro z hz
      refine ⟨Sum.elim (fun j => (z j).re) (fun j => (z j).im), ?_, ?_⟩
      · show MvPolynomial.eval _ (rePoly Q') = 0
        rw [eval_rePoly]
        have hpt : realifyPoint (Sum.elim (fun j => (z j).re) (fun j => (z j).im)) = z := by
          funext j
          exact Complex.ext rfl rfl
        rw [eval_complexSplitSubst, hpt, hz, Complex.zero_re]
      · funext j
        exact Complex.ext rfl rfl
    · refine le_trans (lipschitzWith_realifyPoint.dimH_image_le _) ?_
      refine le_trans (dimH_setOf_eval_eq_zero_le (rePoly Q') hP) ?_
      simp [Fintype.card_sum, two_mul]
  · refine le_trans (dimH_mono (?_ : {z : κ → ℂ | MvPolynomial.eval z Q = 0}
      ⊆ realifyPoint '' {u : (κ ⊕ κ) → ℝ | MvPolynomial.eval u (imPoly Q') = 0})) ?_
    · intro z hz
      refine ⟨Sum.elim (fun j => (z j).re) (fun j => (z j).im), ?_, ?_⟩
      · show MvPolynomial.eval _ (imPoly Q') = 0
        rw [eval_imPoly]
        have hpt : realifyPoint (Sum.elim (fun j => (z j).re) (fun j => (z j).im)) = z := by
          funext j
          exact Complex.ext rfl rfl
        rw [eval_complexSplitSubst, hpt, hz, Complex.zero_im]
      · funext j
        exact Complex.ext rfl rfl
    · refine le_trans (lipschitzWith_realifyPoint.dimH_image_le _) ?_
      refine le_trans (dimH_setOf_eval_eq_zero_le (imPoly Q') hP) ?_
      simp [Fintype.card_sum, two_mul]

/-! ### Partial specialization keeps a polynomial nonzero -/

/-- **A nonzero polynomial stays nonzero after specializing some variables at a good point.**
Evaluating the specialization at the same point recovers the original value, so any point where the
polynomial does not vanish supplies admissible values for the specialized variables. -/
theorem exists_partial_specialization_ne_zero {γ : Type} [Fintype γ] [DecidableEq γ]
    (S : Finset γ) (D : MvPolynomial γ ℂ) (hD : D ≠ 0) :
    ∃ v : γ → ℂ, MvPolynomial.aeval
      (fun g => if g ∈ S then MvPolynomial.C (v g) else MvPolynomial.X g) D ≠ 0 := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : γ → ℂ, MvPolynomial.eval w D ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hD (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
  refine ⟨w, fun hzero => hw ?_⟩
  have hbind : MvPolynomial.aeval
      (fun g => if g ∈ S then MvPolynomial.C (w g) else MvPolynomial.X g) D
      = MvPolynomial.bind₁
        (fun g => if g ∈ S then MvPolynomial.C (w g) else MvPolynomial.X g) D := rfl
  have hev : MvPolynomial.eval w
      (MvPolynomial.aeval (fun g => if g ∈ S then MvPolynomial.C (w g)
        else MvPolynomial.X g) D) = MvPolynomial.eval w D := by
    rw [hbind]
    show MvPolynomial.eval₂Hom (RingHom.id ℂ) w _ = _
    rw [MvPolynomial.eval₂Hom_bind₁]
    show MvPolynomial.eval (fun g => MvPolynomial.eval w
      (if g ∈ S then MvPolynomial.C (w g) else MvPolynomial.X g)) D = _
    have hpt : (fun g => MvPolynomial.eval w
        (if g ∈ S then MvPolynomial.C (w g) else MvPolynomial.X g)) = w := by
      funext g
      by_cases hg : g ∈ S
      · rw [if_pos hg, MvPolynomial.eval_C]
      · rw [if_neg hg, MvPolynomial.eval_X]
    rw [hpt]
  rw [hzero, map_zero] at hev
  exact hev.symm

end

end GaloisForLFunctions.HTGeometry
