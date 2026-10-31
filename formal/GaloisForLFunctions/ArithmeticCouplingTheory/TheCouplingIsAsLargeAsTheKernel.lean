import GaloisForLFunctions.ArithmeticCouplingTheory.TheLocalHyersUlamInequality
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-!
# The coupling is as large as the kernel

Let `Φ : ℝ → ℂ` be a continuous profile (a kernel on a dense group of scales written in
log-coordinates) and `A, B ⊆ ℝ` dense sets of log-scales, e.g. the logarithms of two two-prime
lattices `⟨p, q⟩`, `⟨r, s⟩`. The coupling `C(a, b) = Φ(a + b) − Φ(a) − Φ(b) + Φ(0)` is only sampled
on `A × B`.

* **Density** (`le_of_dense_prod`, `norm_profileCoupling_le_of_dense_box`): any continuous bound on
  `A × B` holds on the whole plane, and a constant bound on the box `|a|, |b| ≤ L` holds on the real
  box. No Diophantine information on `A`, `B` enters.
* **Antidiagonal** (`profileCoupling_neg_of_hermitian`): for a Hermitian profile,
  `C(x, −x) = 2(Φ(0) − Re Φ(x))`. The antidiagonal never meets `A × B` for coprime lattices, but it
  lies in the closure.
* **Lossless transfer** (`abs_re_sub_le_of_dense`): if `|Re C| ≤ g` on `A × B` for a continuous
  `g`, then `|Re Φ(x) − Φ(0)| ≤ g(x, −x)/2` for every real `x`. Conversely the coupling is at most four
  times the kernel (`norm_profileCoupling_le`). The coupling functional and the kernel functional
  are therefore equivalent with absolute constants and no loss in the height.
* **Local stability on dense lattices** (`norm_sub_affine_le_of_dense_box`): a coupling bound `M` on
  the lattice box of height `L` makes `Φ` affine up to `3M` on `[−L, L]`.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- A continuous bound on a dense product set holds everywhere. -/
theorem le_of_dense_prod {F g : ℝ × ℝ → ℝ} (hF : Continuous F) (hg : Continuous g)
    {A B : Set ℝ} (hA : Dense A) (hB : Dense B) (h : ∀ a ∈ A, ∀ b ∈ B, F (a, b) ≤ g (a, b))
    (p : ℝ × ℝ) : F p ≤ g p := by
  have hsub : A ×ˢ B ⊆ {p | F p ≤ g p} := fun q hq => h q.1 hq.1 q.2 hq.2
  have hcl := (isClosed_le hF hg).closure_subset_iff.mpr hsub
  rw [(hA.prod hB).closure_eq] at hcl
  exact hcl (mem_univ p)

theorem continuous_profileCoupling {Φ : ℝ → ℂ} (hΦ : Continuous Φ) :
    Continuous fun p : ℝ × ℝ => profileCoupling Φ p.1 p.2 := by
  unfold profileCoupling; fun_prop

/-- A dense set meets every closed interval densely. -/
theorem Icc_subset_closure_inter {A : Set ℝ} (hA : Dense A) {L : ℝ} (hL : 0 < L) :
    Icc (-L) L ⊆ closure (A ∩ Icc (-L) L) := by
  intro x hx
  have h1 : Ioo (-L) L ⊆ closure (Ioo (-L) L ∩ A) := hA.open_subset_closure_inter isOpen_Ioo
  have h2 : closure (Ioo (-L) L ∩ A) ⊆ closure (A ∩ Icc (-L) L) :=
    closure_mono fun y hy => ⟨hy.2, Ioo_subset_Icc_self hy.1⟩
  have h3 : closure (Ioo (-L) L) ⊆ closure (A ∩ Icc (-L) L) :=
    closure_minimal (h1.trans h2) isClosed_closure
  rw [closure_Ioo (by linarith : -L ≠ L)] at h3
  exact h3 hx

/-- **Density on boxes.** A coupling bound on the lattice box `|a|, |b| ≤ L` holds on the real box. -/
theorem norm_profileCoupling_le_of_dense_box {Φ : ℝ → ℂ} (hΦ : Continuous Φ) {A B : Set ℝ}
    (hA : Dense A) (hB : Dense B) {L M : ℝ} (hL : 0 < L)
    (h : ∀ a ∈ A, ∀ b ∈ B, |a| ≤ L → |b| ≤ L → ‖profileCoupling Φ a b‖ ≤ M)
    {x y : ℝ} (hx : |x| ≤ L) (hy : |y| ≤ L) : ‖profileCoupling Φ x y‖ ≤ M := by
  have hsub : (A ∩ Icc (-L) L) ×ˢ (B ∩ Icc (-L) L) ⊆
      {p : ℝ × ℝ | ‖profileCoupling Φ p.1 p.2‖ ≤ M} := fun p hp =>
    h p.1 hp.1.1 p.2 hp.2.1 (abs_le.mpr hp.1.2) (abs_le.mpr hp.2.2)
  have hcl := (isClosed_le (continuous_profileCoupling hΦ).norm continuous_const).closure_subset_iff.mpr
    hsub
  rw [closure_prod_eq] at hcl
  exact hcl (Set.mk_mem_prod (Icc_subset_closure_inter hA hL (abs_le.mp hx))
    (Icc_subset_closure_inter hB hL (abs_le.mp hy)))

/-- **The antidiagonal identity for profiles.** -/
theorem profileCoupling_neg_of_hermitian {Φ : ℝ → ℂ} (hΦ : ∀ x, Φ (-x) = conj (Φ x)) (x : ℝ) :
    profileCoupling Φ x (-x) = ((2 * ((Φ 0).re - (Φ x).re) : ℝ) : ℂ) := by
  have h0 : (Φ 0).im = 0 := by
    have := congrArg Complex.im (hΦ 0)
    rw [neg_zero, Complex.conj_im] at this
    linarith
  rw [profileCoupling, add_neg_cancel, hΦ x]
  apply Complex.ext
  · simp; ring
  · simp [h0]

/-- **Lossless transfer.** A continuous bound `g` on the real part of the coupling over a dense
product of log-scales bounds the real part of the profile by `g(x, −x)/2`. -/
theorem abs_re_sub_le_of_dense {Φ : ℝ → ℂ} (hΦc : Continuous Φ)
    (hΦ : ∀ x, Φ (-x) = conj (Φ x)) {A B : Set ℝ} (hA : Dense A) (hB : Dense B) {g : ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (h : ∀ a ∈ A, ∀ b ∈ B, |(profileCoupling Φ a b).re| ≤ g a b) (x : ℝ) :
    |(Φ x).re - (Φ 0).re| ≤ g x (-x) / 2 := by
  have hc := le_of_dense_prod (F := fun p => |(profileCoupling Φ p.1 p.2).re|)
    (Complex.continuous_re.comp (continuous_profileCoupling hΦc)).abs hg hA hB
    (fun a ha b hb => h a ha b hb) (x, -x)
  simp only [profileCoupling_neg_of_hermitian hΦ x, Complex.ofReal_re] at hc
  rw [abs_mul, abs_two, abs_sub_comm] at hc
  linarith

/-- The coupling is at most the sum of the four kernel values it reads. -/
theorem norm_profileCoupling_le (Φ : ℝ → ℂ) (x y : ℝ) :
    ‖profileCoupling Φ x y‖ ≤ ‖Φ (x + y)‖ + ‖Φ x‖ + ‖Φ y‖ + ‖Φ 0‖ := by
  unfold profileCoupling
  calc ‖Φ (x + y) - Φ x - Φ y + Φ 0‖ ≤ ‖Φ (x + y) - Φ x - Φ y‖ + ‖Φ 0‖ := norm_add_le _ _
    _ ≤ ‖Φ (x + y) - Φ x‖ + ‖Φ y‖ + ‖Φ 0‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖Φ (x + y)‖ + ‖Φ x‖ + ‖Φ y‖ + ‖Φ 0‖ := by gcongr; exact norm_sub_le _ _

/-- **Local stability on dense lattices.** A coupling bound `M` on the lattice box of height `L`
makes a continuous profile affine up to `3M` on `[−L, L]`. -/
theorem norm_sub_affine_le_of_dense_box {Φ : ℝ → ℂ} (hΦ : Continuous Φ) {A B : Set ℝ}
    (hA : Dense A) (hB : Dense B) {L M : ℝ} (hL : 0 < L)
    (h : ∀ a ∈ A, ∀ b ∈ B, |a| ≤ L → |b| ≤ L → ‖profileCoupling Φ a b‖ ≤ M)
    {x : ℝ} (hx : |x| ≤ L) :
    ‖Φ x - Φ 0 - (x / L) • (Φ L - Φ 0)‖ ≤ 3 * M := by
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := -L) (b := L)).exists_bound_of_continuousOn
    hΦ.continuousOn
  exact norm_profileCoupling_sub_linear_le hL (fun y hy => hS y (abs_le.mp hy))
    (fun y z hy hz _ => norm_profileCoupling_le_of_dense_box hΦ hA hB hL h hy hz) x hx

end GaloisForLFunctions.ArithmeticCouplingTheory
