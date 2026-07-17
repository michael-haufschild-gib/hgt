import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaLogKernel
import Mathlib.Data.Fintype.Option

/-!
# Summability of finite products of nonnegative series

A finite family of nonnegative summable sequences has a summable product family on the finite
Cartesian power.  This is the all-order geometric-majorant lemma for multiple elliptic gamma.
-/

open scoped BigOperators

namespace GaloisForLFunctions

set_option maxHeartbeats 800000 in
private theorem summable_fintype_pi_product_of_nonneg_over
    (ι : Type) [Fintype ι] {β : Type}
    (w : ι → β → ℝ)
    (hs : ∀ i, Summable (w i))
    (hn : ∀ i n, 0 ≤ w i n) :
    Summable (fun a : ι → β => ∏ i, w i (a i)) := by
  classical
  let P : ∀ (α : Type) [Fintype α], Prop := fun α _ =>
    ∀ (w : α → β → ℝ),
      (∀ i, Summable (w i)) →
      (∀ i n, 0 ≤ w i n) →
      Summable (fun a : α → β => ∏ i, w i (a i))
  apply Fintype.induction_empty_option (P := P)
  · intro α γ _ e h w hs hn
    letI : Fintype α := Fintype.ofEquiv γ e.symm
    let W : α → β → ℝ := fun i => w (e i)
    have hW := h W (fun i => hs (e i)) (fun i => hn (e i))
    let he : (α → β) ≃ (γ → β) :=
      { toFun := fun a j => a (e.symm j)
        invFun := fun b i => b (e i)
        left_inv := by intro a; funext i; simp
        right_inv := by intro b; funext j; simp }
    apply (he.summable_iff).1
    convert hW using 1
    funext a
    change (∏ j : γ, w j (a (e.symm j))) = ∏ i : α, w (e i) (a i)
    simpa using
      (Fintype.prod_equiv e
        (fun i : α => w (e i) (a i))
        (fun j : γ => w j (a (e.symm j))) (by intro i; simp)).symm
  · intro w hs hn
    exact Summable.of_finite
  · intro α _ h w hs hn
    let rest : α → β → ℝ := fun i => w (some i)
    have hrest : Summable (fun a : α → β => ∏ i, rest i (a i)) :=
      h rest (fun i => hs (some i)) (fun i => hn (some i))
    have hprod : Summable (fun ka : β × (α → β) =>
        w none ka.1 * ∏ i, rest i (ka.2 i)) :=
      (hs none).mul_of_nonneg hrest (hn none)
        (fun a => Finset.prod_nonneg fun i _ => hn (some i) (a i))
    let e : (Option α → β) ≃ β × (α → β) := Equiv.piOptionEquivProd
    have heSum := (e.summable_iff).2 hprod
    convert heSum using 1
    funext a
    rw [Fintype.prod_option]
    rfl
  · exact hs
  · exact hn

/-- Finite products of nonnegative summable sequences are summable over the corresponding
function space. -/
theorem summable_fintype_pi_product_of_nonneg
    (ι : Type) [Fintype ι]
    (w : ι → ℕ → ℝ)
    (hs : ∀ i, Summable (w i))
    (hn : ∀ i n, 0 ≤ w i n) :
    Summable (fun a : ι → ℕ => ∏ i, w i (a i)) :=
  summable_fintype_pi_product_of_nonneg_over ι w hs hn

/-- Polynomially weighted Gaussians are summable over the natural numbers. -/
theorem summable_pow_mul_exp_neg_nat_sq (A : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Summable (fun n : ℕ => (n : ℝ) ^ A * Real.exp (-sigma * (n : ℝ) ^ 2)) := by
  have hgeom : Summable (fun n : ℕ =>
      (n : ℝ) ^ A * Real.exp (-((n : ℝ) * sigma))) := by
    have hr : ‖Real.exp (-sigma)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    refine (summable_pow_mul_geometric_of_norm_lt_one (k := A) hr).congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeom
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ n =>
        have h1 : (1 : ℝ) ≤ (n.succ : ℕ) := by exact_mod_cast n.succ_pos
        nlinarith
  gcongr
  nlinarith

/-- Adding one to the polynomial weight preserves discrete Gaussian summability. -/
theorem summable_one_add_pow_mul_exp_neg_nat_sq
    (A : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Summable (fun n : ℕ => (1 + (n : ℝ)) ^ A * Real.exp (-sigma * (n : ℝ) ^ 2)) := by
  rw [← summable_nat_add_iff 1]
  have hbase := (summable_nat_add_iff 1).mpr
    ((summable_pow_mul_exp_neg_nat_sq A hsigma).mul_left ((2 : ℝ) ^ A))
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  have hn : (1 + ((n + 1 : ℕ) : ℝ)) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + (n + 1 : ℕ)) hn A
  calc
    (1 + ((n + 1 : ℕ) : ℝ)) ^ A *
          Real.exp (-sigma * ((n + 1 : ℕ) : ℝ) ^ 2)
        ≤ (2 * ((n + 1 : ℕ) : ℝ)) ^ A *
          Real.exp (-sigma * ((n + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (2 : ℝ) ^ A *
          (((n + 1 : ℕ) : ℝ) ^ A *
            Real.exp (-sigma * ((n + 1 : ℕ) : ℝ) ^ 2)) := by ring

/-- Polynomially weighted Gaussians are summable over the integers. -/
theorem summable_one_add_natAbs_pow_mul_exp_neg_int_sq
    (A : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Summable (fun z : ℤ =>
      (1 + (z.natAbs : ℝ)) ^ A * Real.exp (-sigma * (z : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor <;> simpa using summable_one_add_pow_mul_exp_neg_nat_sq A hsigma

set_option maxHeartbeats 800000 in
/-- Every finite-dimensional integer lattice has summable coordinatewise-polynomial Gaussian
weight with arbitrary positive coordinate decay rates. -/
theorem summable_fintype_pi_polynomialGaussian
    (ι : Type) [Fintype ι] (A : ι → ℕ) (sigma : ι → ℝ)
    (hsigma : ∀ i, 0 < sigma i) :
    Summable (fun z : ι → ℤ =>
      ∏ i, (1 + ((z i).natAbs : ℝ)) ^ A i *
        Real.exp (-sigma i * (z i : ℝ) ^ 2)) := by
  let w : ι → ℤ → ℝ := fun i z =>
    (1 + (z.natAbs : ℝ)) ^ A i * Real.exp (-sigma i * (z : ℝ) ^ 2)
  change Summable (fun z : ι → ℤ => ∏ i, w i (z i))
  exact summable_fintype_pi_product_of_nonneg_over ι w
    (fun i => summable_one_add_natAbs_pow_mul_exp_neg_int_sq (A i) (hsigma i))
    (fun _ _ => by dsimp [w]; positivity)

/-- The finite box of integer lattice points whose coordinates lie in `[-R,R]`. -/
noncomputable def integerLatticeBox (ι : Type) [Fintype ι] (R : ℕ) : Finset (ι → ℤ) :=
  (Set.Finite.pi (fun _ : ι => Set.finite_Icc (-(R : ℤ)) (R : ℤ))).toFinset

@[simp] theorem mem_integerLatticeBox_iff
    (ι : Type) [Fintype ι] (R : ℕ) (z : ι → ℤ) :
    z ∈ integerLatticeBox ι R ↔ ∀ i, -(R : ℤ) ≤ z i ∧ z i ≤ (R : ℤ) := by
  classical
  simp only [integerLatticeBox, Set.Finite.mem_toFinset, Set.mem_univ, Set.mem_pi,
    Set.mem_Icc, true_implies]

private def finiteLatticeRadius
    {ι : Type} [Fintype ι] (s : Finset (ι → ℤ)) : ℕ :=
  s.sup fun z => Finset.univ.sup fun i => (z i).natAbs

/-- Finite integer boxes exhaust every finite-dimensional integer lattice. -/
theorem integerLatticeBox_tendsto_atTop (ι : Type) [Fintype ι] :
    Filter.Tendsto (integerLatticeBox ι) Filter.atTop Filter.atTop := by
  classical
  apply Filter.tendsto_atTop.2
  intro s
  filter_upwards [Filter.eventually_ge_atTop (finiteLatticeRadius s)] with R hR
  intro z hz
  rw [mem_integerLatticeBox_iff]
  intro i
  have hi : (z i).natAbs ≤ Finset.univ.sup fun j => (z j).natAbs :=
    Finset.le_sup (f := fun j : ι => (z j).natAbs) (Finset.mem_univ i)
  have hzsup : (Finset.univ.sup fun j => (z j).natAbs) ≤ finiteLatticeRadius s :=
    Finset.le_sup (f := fun y : ι → ℤ =>
      Finset.univ.sup fun j => (y j).natAbs) hz
  have hnat : (z i).natAbs ≤ R := hi.trans (hzsup.trans hR)
  have hint : ((z i).natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast hnat
  rw [Int.natCast_natAbs] at hint
  exact abs_le.mp hint

/-- The polynomial-Gaussian mass outside the finite integer box tends to zero. -/
theorem tendsto_polynomialGaussian_tsum_outside_box_zero
    (ι : Type) [Fintype ι] (A : ι → ℕ) (sigma : ι → ℝ) :
    Filter.Tendsto (fun R =>
      ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
        ∏ i, (1 + ((z.1 i).natAbs : ℝ)) ^ A i *
          Real.exp (-sigma i * (z.1 i : ℝ) ^ 2))
      Filter.atTop (nhds 0) := by
  exact (tendsto_tsum_compl_atTop_zero (fun z : ι → ℤ =>
    ∏ i, (1 + ((z i).natAbs : ℝ)) ^ A i *
      Real.exp (-sigma i * (z i : ℝ) ^ 2))).comp
        (integerLatticeBox_tendsto_atTop ι)

end GaloisForLFunctions
