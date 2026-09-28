import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Bilateral exponentially weighted convolution algebras

For `a ≥ 0` the sequences `x : ℤ → ℂ` with `∑ e^{a|k|} |x_k| < ∞` form a commutative unital
Banach algebra `𝒜_a` under Cauchy convolution `(x * y)_n = ∑_j x_j y_{n-j}`; the weight is
submultiplicative, so `‖x * y‖_a ≤ ‖x‖_a ‖y‖_a`, and the weight isometry onto `ℓ¹(ℤ)` makes the
algebra complete.
-/

namespace GaloisForLFunctions.HTGeometry.BilateralRepair

noncomputable section

open Filter Topology

/-! ## The bilateral exponential weight -/

/-- The weight `e^{a|k|}`. -/
def expWeight (a : ℝ) (k : ℤ) : ℝ := Real.exp (a * |(k : ℝ)|)

theorem expWeight_pos (a : ℝ) (k : ℤ) : 0 < expWeight a k := Real.exp_pos _

theorem one_le_expWeight {a : ℝ} (ha : 0 ≤ a) (k : ℤ) : 1 ≤ expWeight a k :=
  Real.one_le_exp (mul_nonneg ha (abs_nonneg _))

theorem expWeight_add_le {a : ℝ} (ha : 0 ≤ a) (j m : ℤ) :
    expWeight a (j + m) ≤ expWeight a j * expWeight a m := by
  rw [expWeight, expWeight, expWeight, ← Real.exp_add, Real.exp_le_exp]
  push_cast
  have := abs_add_le (j : ℝ) m
  nlinarith

theorem expWeight_neg (a : ℝ) (k : ℤ) : expWeight a (-k) = expWeight a k := by
  simp [expWeight, abs_neg]

theorem expWeight_mono {a b : ℝ} (hab : a ≤ b) (k : ℤ) : expWeight a k ≤ expWeight b k :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab (abs_nonneg _))

theorem expWeight_zero_index (a : ℝ) : expWeight a 0 = 1 := by simp [expWeight]

/-! ## Admissible sequences and the weighted norm -/

/-- `x` has finite `a`-weighted absolute mass. -/
def Admissible (a : ℝ) (x : ℤ → ℂ) : Prop := Summable fun k => expWeight a k * ‖x k‖

/-- The weighted norm `∑ e^{a|k|} |x_k|`. -/
def wnorm (a : ℝ) (x : ℤ → ℂ) : ℝ := ∑' k, expWeight a k * ‖x k‖

theorem wnorm_nonneg (a : ℝ) (x : ℤ → ℂ) : 0 ≤ wnorm a x :=
  tsum_nonneg fun k => mul_nonneg (expWeight_pos a k).le (norm_nonneg _)

theorem Admissible.summable_norm {a : ℝ} (ha : 0 ≤ a) {x : ℤ → ℂ} (hx : Admissible a x) :
    Summable fun k => ‖x k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => le_mul_of_one_le_left (norm_nonneg _) (one_le_expWeight ha k)) hx

theorem Admissible.norm_le {a : ℝ} (ha : 0 ≤ a) {x : ℤ → ℂ} (hx : Admissible a x) (k : ℤ) :
    ‖x k‖ ≤ wnorm a x :=
  (le_mul_of_one_le_left (norm_nonneg _) (one_le_expWeight ha k)).trans
    (hx.le_tsum k fun j _ => mul_nonneg (expWeight_pos a j).le (norm_nonneg _))

theorem admissible_zero (a : ℝ) : Admissible a 0 := by
  simp [Admissible]

theorem Admissible.add {a : ℝ} {x y : ℤ → ℂ} (hx : Admissible a x) (hy : Admissible a y) :
    Admissible a (x + y) :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (expWeight_pos a k).le (norm_nonneg _))
    (fun k => by
      rw [Pi.add_apply, ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (expWeight_pos a k).le)
    (Summable.add hx hy)

theorem Admissible.smul {a : ℝ} {x : ℤ → ℂ} (hx : Admissible a x) (c : ℂ) :
    Admissible a (c • x) := by
  refine (hx.mul_left ‖c‖).congr fun k => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

theorem wnorm_add_le {a : ℝ} {x y : ℤ → ℂ} (hx : Admissible a x) (hy : Admissible a y) :
    wnorm a (x + y) ≤ wnorm a x + wnorm a y := by
  rw [wnorm, wnorm, wnorm, ← Summable.tsum_add hx hy]
  refine Summable.tsum_le_tsum (fun k => ?_) (Admissible.add hx hy) (Summable.add hx hy)
  rw [Pi.add_apply, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (expWeight_pos a k).le

/-! ## Cauchy convolution -/

/-- Cauchy convolution `(x * y)_n = ∑_j x_j y_{n-j}`. -/
def conv (x y : ℤ → ℂ) (n : ℤ) : ℂ := ∑' j, x j * y (n - j)

/-- The shear `(n, j) ↦ (j, n - j)`. -/
def shear : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, p.1 - p.2)
  invFun q := (q.1 + q.2, q.1)
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

/-- The absolute majorant of a convolution, indexed by `(n, j)`. -/
def convMajorant (a : ℝ) (x y : ℤ → ℂ) (p : ℤ × ℤ) : ℝ :=
  expWeight a p.2 * ‖x p.2‖ * (expWeight a (p.1 - p.2) * ‖y (p.1 - p.2)‖)

theorem convMajorant_nonneg (a : ℝ) (x y : ℤ → ℂ) (p : ℤ × ℤ) : 0 ≤ convMajorant a x y p := by
  unfold convMajorant
  have := expWeight_pos a p.2
  have := expWeight_pos a (p.1 - p.2)
  positivity

theorem summable_convMajorant {a : ℝ} {x y : ℤ → ℂ} (hx : Admissible a x)
    (hy : Admissible a y) : Summable (convMajorant a x y) := by
  have hF := Summable.mul_of_nonneg hx hy
    (fun k => mul_nonneg (expWeight_pos a k).le (norm_nonneg _))
    (fun k => mul_nonneg (expWeight_pos a k).le (norm_nonneg _))
  exact (shear.summable_iff).mpr hF

theorem tsum_convMajorant {a : ℝ} {x y : ℤ → ℂ} (hx : Admissible a x) (hy : Admissible a y) :
    ∑' p, convMajorant a x y p = wnorm a x * wnorm a y := by
  have hnx : Summable fun k => ‖expWeight a k * ‖x k‖‖ := by
    simpa only [Real.norm_eq_abs] using Summable.abs hx
  have hny : Summable fun k => ‖expWeight a k * ‖y k‖‖ := by
    simpa only [Real.norm_eq_abs] using Summable.abs hy
  rw [wnorm, wnorm, tsum_mul_tsum_of_summable_norm hnx hny]
  exact shear.tsum_eq (fun q : ℤ × ℤ => expWeight a q.1 * ‖x q.1‖ * (expWeight a q.2 * ‖y q.2‖))

theorem norm_conv_term_le {a : ℝ} (ha : 0 ≤ a) (x y : ℤ → ℂ) (n j : ℤ) :
    ‖x j * y (n - j)‖ ≤ convMajorant a x y (n, j) := by
  unfold convMajorant
  rw [norm_mul]
  have h1 := one_le_expWeight ha j
  have h2 := one_le_expWeight ha (n - j)
  have hx := norm_nonneg (x j)
  have hy := norm_nonneg (y (n - j))
  calc ‖x j‖ * ‖y (n - j)‖ = (1 * ‖x j‖) * (1 * ‖y (n - j)‖) := by ring
    _ ≤ _ := by gcongr

theorem summable_conv_term {a : ℝ} (ha : 0 ≤ a) {x y : ℤ → ℂ} (hx : Admissible a x)
    (hy : Admissible a y) (n : ℤ) : Summable fun j => x j * y (n - j) :=
  Summable.of_norm_bounded ((summable_convMajorant hx hy).prod_factor n)
    (norm_conv_term_le ha x y n)

theorem weighted_norm_conv_le {a : ℝ} (ha : 0 ≤ a) {x y : ℤ → ℂ} (hx : Admissible a x)
    (hy : Admissible a y) (n : ℤ) :
    expWeight a n * ‖conv x y n‖ ≤ ∑' j, convMajorant a x y (n, j) := by
  have hsum := (summable_convMajorant hx hy).prod_factor n
  have hterm : Summable fun j => ‖x j * y (n - j)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_conv_term_le ha x y n) hsum
  calc expWeight a n * ‖conv x y n‖
      ≤ expWeight a n * ∑' j, ‖x j * y (n - j)‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hterm) (expWeight_pos a n).le
    _ = ∑' j, expWeight a n * ‖x j * y (n - j)‖ := (tsum_mul_left).symm
    _ ≤ ∑' j, convMajorant a x y (n, j) := by
        refine (hterm.mul_left _).tsum_le_tsum (fun j => ?_) hsum
        unfold convMajorant
        rw [norm_mul]
        have hw := expWeight_add_le ha j (n - j)
        rw [show j + (n - j) = n by ring] at hw
        have hx := norm_nonneg (x j)
        have hy := norm_nonneg (y (n - j))
        calc expWeight a n * (‖x j‖ * ‖y (n - j)‖)
            ≤ expWeight a j * expWeight a (n - j) * (‖x j‖ * ‖y (n - j)‖) :=
              mul_le_mul_of_nonneg_right hw (by positivity)
          _ = _ := by ring

/-- **Convolution preserves admissibility.** -/
theorem Admissible.conv {a : ℝ} (ha : 0 ≤ a) {x y : ℤ → ℂ} (hx : Admissible a x)
    (hy : Admissible a y) : Admissible a (conv x y) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (expWeight_pos a n).le (norm_nonneg _))
    (weighted_norm_conv_le ha hx hy) (summable_convMajorant hx hy).prod

/-- **(BER.5)** Submultiplicativity `‖x * y‖_a ≤ ‖x‖_a ‖y‖_a`. -/
theorem wnorm_conv_le {a : ℝ} (ha : 0 ≤ a) {x y : ℤ → ℂ} (hx : Admissible a x)
    (hy : Admissible a y) : wnorm a (conv x y) ≤ wnorm a x * wnorm a y := by
  rw [← tsum_convMajorant hx hy, (summable_convMajorant hx hy).tsum_prod]
  exact (hx.conv ha hy).tsum_le_tsum (weighted_norm_conv_le ha hx hy)
    (summable_convMajorant hx hy).prod

/-! ## Algebra laws of convolution -/

theorem conv_comm (x y : ℤ → ℂ) : conv x y = conv y x := by
  funext n
  unfold conv
  rw [← (Equiv.subLeft n).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

/-- The unit atom `δ₀`. -/
def unitSeq : ℤ → ℂ := fun k => if k = 0 then 1 else 0

theorem admissible_unitSeq (a : ℝ) : Admissible a unitSeq := by
  refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
  rw [Finset.mem_singleton] at hk
  simp [unitSeq, hk]

theorem wnorm_unitSeq (a : ℝ) : wnorm a unitSeq = 1 := by
  rw [wnorm, tsum_eq_single 0]
  · simp [unitSeq, expWeight_zero_index]
  · intro k hk; simp [unitSeq, hk]

theorem conv_unitSeq (x : ℤ → ℂ) : conv x unitSeq = x := by
  funext n
  unfold conv
  rw [tsum_eq_single n]
  · simp [unitSeq]
  · intro j hj
    have : n - j ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
    simp [unitSeq, this]

theorem unitSeq_conv (x : ℤ → ℂ) : conv unitSeq x = x := by
  rw [conv_comm, conv_unitSeq]

theorem conv_add_left {a : ℝ} (ha : 0 ≤ a) {x x' y : ℤ → ℂ} (hx : Admissible a x)
    (hx' : Admissible a x') (hy : Admissible a y) :
    conv (x + x') y = conv x y + conv x' y := by
  funext n
  simp only [conv, Pi.add_apply, add_mul]
  exact Summable.tsum_add (summable_conv_term ha hx hy n) (summable_conv_term ha hx' hy n)

theorem conv_smul_left (c : ℂ) (x y : ℤ → ℂ) : conv (c • x) y = c • conv x y := by
  funext n
  simp only [conv, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem conv_zero_left (y : ℤ → ℂ) : conv 0 y = 0 := by
  funext n; simp [conv]

theorem conv_assoc {a : ℝ} (ha : 0 ≤ a) {x y z : ℤ → ℂ} (hx : Admissible a x)
    (hy : Admissible a y) (hz : Admissible a z) :
    conv (conv x y) z = conv x (conv y z) := by
  funext n
  set Ψ : ℤ × ℤ → ℂ := fun q => x q.1 * (y q.2 * z (n - q.1 - q.2)) with hΨdef
  have hΦΨ : (fun p : ℤ × ℤ => x p.2 * y (p.1 - p.2) * z (n - p.1)) = Ψ ∘ shear := by
    funext p
    simp only [Function.comp_apply, hΨdef, shear, Equiv.coe_fn_mk]
    rw [show n - p.2 - (p.1 - p.2) = n - p.1 by ring, mul_assoc]
  have hΦ : Summable fun p : ℤ × ℤ => x p.2 * y (p.1 - p.2) * z (n - p.1) := by
    have hprod := Summable.mul_of_nonneg (hx.summable_norm ha) (hy.summable_norm ha)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have hsh : Summable fun p : ℤ × ℤ => ‖x p.2‖ * ‖y (p.1 - p.2)‖ :=
      (shear.summable_iff).mpr hprod
    refine Summable.of_norm_bounded (hsh.mul_right (wnorm a z)) fun p => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hz.norm_le ha _) (by positivity)
  have hΨ : Summable Ψ := by
    rw [← shear.summable_iff, ← hΦΨ]; exact hΦ
  have hL : conv (conv x y) z n = ∑' p : ℤ × ℤ, x p.2 * y (p.1 - p.2) * z (n - p.1) := by
    rw [hΦ.tsum_prod]
    unfold conv
    exact tsum_congr fun i => (tsum_mul_right).symm
  have hR : conv x (conv y z) n = ∑' q, Ψ q := by
    rw [hΨ.tsum_prod]
    unfold conv
    refine tsum_congr fun j => ?_
    rw [← tsum_mul_left]
  rw [hL, hR, hΦΨ]
  exact shear.tsum_eq Ψ

/-! ## The Banach algebra `𝒜_a` -/

/-- Admissible sequences of grade `a` as a submodule of all bilateral sequences. -/
def fibreSubmodule (a : ℝ) : Submodule ℂ (ℤ → ℂ) where
  carrier := {x | Admissible a x}
  add_mem' hx hy := Admissible.add hx hy
  zero_mem' := admissible_zero a
  smul_mem' c _ hx := hx.smul c

/-- The bilateral exponentially weighted convolution algebra `𝒜_a`. -/
def Fibre (a : ℝ) : Type := ↥(fibreSubmodule a)

namespace Fibre

variable {a : ℝ}

instance : AddCommGroup (Fibre a) := inferInstanceAs (AddCommGroup ↥(fibreSubmodule a))

instance : Module ℂ (Fibre a) := inferInstanceAs (Module ℂ ↥(fibreSubmodule a))

/-- The underlying bilateral sequence. -/
def seq (x : Fibre a) : ℤ → ℂ := x.1

theorem admissible (x : Fibre a) : Admissible a x.seq := x.2

@[ext] theorem ext {x y : Fibre a} (h : x.seq = y.seq) : x = y := Subtype.ext h

/-- Construct an element from an admissible sequence. -/
def mk (x : ℤ → ℂ) (hx : Admissible a x) : Fibre a := ⟨x, hx⟩

@[simp] theorem seq_mk (x : ℤ → ℂ) (hx : Admissible a x) : (mk x hx).seq = x := rfl

@[simp] theorem seq_zero : (0 : Fibre a).seq = 0 := rfl

@[simp] theorem seq_add (x y : Fibre a) : (x + y).seq = x.seq + y.seq := rfl

@[simp] theorem seq_neg (x : Fibre a) : (-x).seq = -x.seq := rfl

@[simp] theorem seq_sub (x y : Fibre a) : (x - y).seq = x.seq - y.seq := rfl

@[simp] theorem seq_smul (c : ℂ) (x : Fibre a) : (c • x).seq = c • x.seq := rfl

variable [ha : Fact (0 ≤ a)]

instance : Mul (Fibre a) := ⟨fun x y => mk (conv x.seq y.seq) (x.admissible.conv ha.out y.admissible)⟩

instance : One (Fibre a) := ⟨mk unitSeq (admissible_unitSeq a)⟩

@[simp] theorem seq_mul (x y : Fibre a) : (x * y).seq = conv x.seq y.seq := rfl

omit ha in
@[simp] theorem seq_one [Fact (0 ≤ a)] : (1 : Fibre a).seq = unitSeq := rfl

instance : CommRing (Fibre a) :=
  { (inferInstance : AddCommGroup (Fibre a)) with
    mul_assoc := fun x y z => ext (by
      simp only [seq_mul]; exact conv_assoc ha.out x.admissible y.admissible z.admissible)
    one_mul := fun x => ext (by simp only [seq_mul, seq_one]; exact unitSeq_conv _)
    mul_one := fun x => ext (by simp only [seq_mul, seq_one]; exact conv_unitSeq _)
    left_distrib := fun x y z => ext (by
      simp only [seq_mul, seq_add]
      rw [conv_comm, conv_add_left ha.out y.admissible z.admissible x.admissible, conv_comm,
        conv_comm z.seq])
    right_distrib := fun x y z => ext (by
      simp only [seq_mul, seq_add]
      exact conv_add_left ha.out x.admissible y.admissible z.admissible)
    zero_mul := fun x => ext (by simp only [seq_mul, seq_zero]; exact conv_zero_left _)
    mul_zero := fun x => ext (by
      simp only [seq_mul, seq_zero]; rw [conv_comm]; exact conv_zero_left _)
    mul_comm := fun x y => ext (by simp only [seq_mul]; exact conv_comm _ _) }

instance : Algebra ℂ (Fibre a) :=
  Algebra.ofModule
    (fun c x y => ext (by simp only [seq_mul, seq_smul]; exact conv_smul_left c _ _))
    (fun c x y => ext (by
      simp only [seq_mul, seq_smul]
      rw [conv_comm, conv_smul_left, conv_comm]))

/-- The weighted norm as an additive group norm. -/
def groupNorm : AddGroupNorm (Fibre a) where
  toFun x := wnorm a x.seq
  map_zero' := by simp [wnorm]
  add_le' x y := wnorm_add_le x.admissible y.admissible
  neg' x := by simp [wnorm]
  eq_zero_of_map_eq_zero' x h := by
    refine ext (funext fun k => ?_)
    have hle := x.admissible.norm_le ha.out k
    rw [h] at hle
    simpa using norm_le_zero_iff.mp hle

instance : NormedAddCommGroup (Fibre a) := groupNorm.toNormedAddCommGroup

theorem norm_def (x : Fibre a) : ‖x‖ = wnorm a x.seq := rfl

instance : NormedCommRing (Fibre a) :=
  { (inferInstance : CommRing (Fibre a)), (inferInstance : NormedAddCommGroup (Fibre a)) with
    norm_mul_le := fun x y => by
      rw [norm_def, norm_def, norm_def, seq_mul]
      exact wnorm_conv_le ha.out x.admissible y.admissible }

instance : NormedAlgebra ℂ (Fibre a) :=
  { (inferInstance : Algebra ℂ (Fibre a)) with
    norm_smul_le := fun c x => by
      rw [norm_def, norm_def, seq_smul, wnorm, wnorm, ← tsum_mul_left]
      refine le_of_eq (tsum_congr fun k => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      ring }

theorem norm_one_eq : ‖(1 : Fibre a)‖ = 1 := wnorm_unitSeq a

/-- The weight coordinates `e^{a|k|} x_k`. -/
def weightCoord (x : Fibre a) (k : ℤ) : ℂ := (expWeight a k : ℂ) * x.seq k

omit ha in
theorem memℓp_weightCoord (x : Fibre a) : Memℓp (weightCoord x) 1 := by
  refine memℓp_gen ?_
  refine x.admissible.congr fun k => ?_
  rw [weightCoord, ENNReal.toReal_one, Real.rpow_one, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (expWeight_pos a k)]

/-- The weight isometry onto `ℓ¹(ℤ)`. -/
def toLp (x : Fibre a) : lp (fun _ : ℤ => ℂ) 1 := ⟨weightCoord x, memℓp_weightCoord x⟩

theorem norm_toLp (x : Fibre a) : ‖toLp x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal), norm_def, wnorm]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]
  refine tsum_congr fun k => ?_
  change ‖weightCoord x k‖ = _
  rw [weightCoord, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (expWeight_pos a k)]

/-- Inverse of the weight isometry. -/
def ofLp (y : lp (fun _ : ℤ => ℂ) 1) : Fibre a :=
  mk (fun k => (y : ℤ → ℂ) k / (expWeight a k : ℂ)) (by
    have hy : Summable fun k => ‖(y : ℤ → ℂ) k‖ := by
      simpa using (lp.memℓp y).summable (by norm_num : 0 < (1 : ENNReal).toReal)
    refine hy.congr fun k => ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (expWeight_pos a k)]
    field_simp [(expWeight_pos a k).ne'])

/-- `𝒜_a` is isometric to `ℓ¹(ℤ)`. -/
def isometryEquivLp : Fibre a ≃ᵢ lp (fun _ : ℤ => ℂ) 1 where
  toFun := toLp
  invFun := ofLp
  left_inv x := ext (funext fun k => by
    simp only [ofLp, seq_mk, toLp, weightCoord]
    change (expWeight a k : ℂ) * x.seq k / (expWeight a k : ℂ) = x.seq k
    field_simp [Complex.ofReal_ne_zero.mpr (expWeight_pos a k).ne'])
  right_inv y := by
    refine lp.ext (funext fun k => ?_)
    change weightCoord (ofLp y) k = (y : ℤ → ℂ) k
    simp only [weightCoord, ofLp, seq_mk]
    field_simp [Complex.ofReal_ne_zero.mpr (expWeight_pos a k).ne']
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    have hsub : toLp x - toLp y = toLp (x - y) := by
      refine lp.ext (funext fun k => ?_)
      change weightCoord x k - weightCoord y k = weightCoord (x - y) k
      simp only [weightCoord, seq_sub, Pi.sub_apply, mul_sub]
    rw [dist_eq_norm, dist_eq_norm, hsub, norm_toLp]

/-- **Theorem 2.1**  `𝒜_a` is complete: a commutative unital Banach algebra. -/
instance : CompleteSpace (Fibre a) := isometryEquivLp.completeSpace

end Fibre

/-! ## Atoms, exponential reporters, and the exact strip -/

/-- The atom `δ_k`. -/
def atomSeq (k : ℤ) : ℤ → ℂ := fun j => if j = k then 1 else 0

theorem admissible_atomSeq (a : ℝ) (k : ℤ) : Admissible a (atomSeq k) := by
  refine summable_of_ne_finset_zero (s := {k}) fun j hj => ?_
  rw [Finset.mem_singleton] at hj
  simp [atomSeq, hj]

theorem wnorm_atomSeq (a : ℝ) (k : ℤ) : wnorm a (atomSeq k) = expWeight a k := by
  rw [wnorm, tsum_eq_single k]
  · simp [atomSeq]
  · intro j hj; simp [atomSeq, hj]

/-- The exponential reporter coefficient `e^{zk}`. -/
def reporterCoeff (z : ℂ) (k : ℤ) : ℂ := Complex.exp (z * k)

theorem norm_reporterCoeff (z : ℂ) (k : ℤ) : ‖reporterCoeff z k‖ = Real.exp (z.re * k) := by
  rw [reporterCoeff, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem norm_reporterCoeff_le {a : ℝ} {z : ℂ} (hz : |z.re| ≤ a) (k : ℤ) :
    ‖reporterCoeff z k‖ ≤ expWeight a k := by
  rw [norm_reporterCoeff, expWeight, Real.exp_le_exp]
  calc z.re * k ≤ |z.re * k| := le_abs_self _
    _ = |z.re| * |(k : ℝ)| := abs_mul _ _
    _ ≤ a * |(k : ℝ)| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)

/-- The exponential reporter `χ_z(x) = ∑ x_k e^{zk}` on sequences. -/
def reporter (z : ℂ) (x : ℤ → ℂ) : ℂ := ∑' k, x k * reporterCoeff z k

theorem summable_reporter {a : ℝ} {z : ℂ} (hz : |z.re| ≤ a) {x : ℤ → ℂ} (hx : Admissible a x) :
    Summable fun k => x k * reporterCoeff z k :=
  Summable.of_norm_bounded hx fun k => by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_reporterCoeff_le hz k) (norm_nonneg _)

theorem norm_reporter_le {a : ℝ} {z : ℂ} (hz : |z.re| ≤ a) {x : ℤ → ℂ} (hx : Admissible a x) :
    ‖reporter z x‖ ≤ wnorm a x := by
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (norm_reporterCoeff_le hz k) (norm_nonneg _)) hx
  · refine Summable.tsum_le_tsum (fun k => ?_) ?_ hx
    · rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (norm_reporterCoeff_le hz k) (norm_nonneg _)
    · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (norm_reporterCoeff_le hz k) (norm_nonneg _)) hx

theorem reporter_atomSeq (z : ℂ) (k : ℤ) : reporter z (atomSeq k) = reporterCoeff z k := by
  rw [reporter, tsum_eq_single k]
  · simp [atomSeq]
  · intro j hj; simp [atomSeq, hj]

theorem reporter_unitSeq (z : ℂ) : reporter z unitSeq = 1 := by
  rw [reporter, tsum_eq_single 0]
  · simp [unitSeq, reporterCoeff]
  · intro j hj; simp [unitSeq, hj]

theorem reporterCoeff_add (z : ℂ) (j m : ℤ) :
    reporterCoeff z (j + m) = reporterCoeff z j * reporterCoeff z m := by
  rw [reporterCoeff, reporterCoeff, reporterCoeff, ← Complex.exp_add]
  push_cast; ring_nf

/-- The reporter is multiplicative on the strip. -/
theorem reporter_conv {a : ℝ} {z : ℂ} (hz : |z.re| ≤ a) {x y : ℤ → ℂ}
    (hx : Admissible a x) (hy : Admissible a y) :
    reporter z (conv x y) = reporter z x * reporter z y := by
  have hnx : Summable fun k => ‖x k * reporterCoeff z k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (norm_reporterCoeff_le hz k) (norm_nonneg _)) hx
  have hny : Summable fun k => ‖y k * reporterCoeff z k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (norm_reporterCoeff_le hz k) (norm_nonneg _)) hy
  have hG : Summable fun p : ℤ × ℤ =>
      x p.2 * reporterCoeff z p.2 * (y (p.1 - p.2) * reporterCoeff z (p.1 - p.2)) := by
    have hprod := Summable.mul_of_nonneg hnx hny (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)
    have hsh := (shear.summable_iff).mpr hprod
    refine Summable.of_norm (hsh.congr fun p => ?_)
    simp only [Function.comp_apply, shear, Equiv.coe_fn_mk, norm_mul]
  unfold reporter
  rw [tsum_mul_tsum_of_summable_norm hnx hny, ← shear.tsum_eq]
  simp only [shear, Equiv.coe_fn_mk]
  rw [hG.tsum_prod]
  unfold conv
  refine tsum_congr fun n => ?_
  rw [← tsum_mul_right]
  refine tsum_congr fun j => ?_
  rw [show reporterCoeff z n = reporterCoeff z j * reporterCoeff z (n - j) by
    rw [← reporterCoeff_add]; congr 1; ring]
  ring


end

end GaloisForLFunctions.HTGeometry.BilateralRepair
