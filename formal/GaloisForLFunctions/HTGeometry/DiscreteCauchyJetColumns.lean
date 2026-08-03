import GaloisForLFunctions.HTGeometry.CauchyTransformIteratedDeriv
import GaloisForLFunctions.HTGeometry.CountableWeightedDirac
import GaloisForLFunctions.HTGeometry.CauchyJetReach

/-!
# The jets of a discrete Cauchy transform are mass-weighted columns

Integrating a kernel power against a countable weighted Dirac family is summing the kernel over the
atoms with the masses as coefficients.  Combined with the factorial dictionary between iterated
derivatives of the Cauchy transform and kernel moments, this says that the whole finite jet packet of
a discrete Cauchy transform is a mass-weighted sum of the controllability columns, one column per
atom.

Moving the masses therefore moves the jet packet linearly, which is what makes the reach lemma
applicable to the actual analytic object.
-/

open MeasureTheory
open _root_.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Bochner integration against a countable weighted Dirac family**, for a Banach-valued
integrand. -/
theorem integral_countableWeightedDirac_vector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {w x : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {f : ℝ → E}
    (hint : Integrable f (countableWeightedDirac w x)) :
    ∫ y, f y ∂(countableWeightedDirac w x) = ∑' n, w n • f (x n) := by
  rw [countableWeightedDirac] at hint ⊢
  rw [integral_sum_measure hint]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw n)]

/-- **A kernel moment of a discrete measure is the mass-weighted column sum.** -/
theorem cauchyKernelMoment_countableWeightedDirac {w x : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    [IsFiniteMeasure (countableWeightedDirac w x)] (k : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    cauchyKernelMoment (countableWeightedDirac w x) k z
      = ∑' n, (w n : ℂ) * (((x n : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) := by
  rw [cauchyKernelMoment,
    integral_countableWeightedDirac_vector hw (integrable_kernelPow _ hz k)]
  refine tsum_congr fun n => ?_
  rw [Complex.real_smul]

/-- **The jets of a discrete Cauchy transform are mass-weighted columns.**  Each derivative order is
a factorial multiple of the sum of the controllability columns against the masses. -/
theorem iteratedDeriv_cauchyTransform_countableWeightedDirac {w x : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    [IsFiniteMeasure (countableWeightedDirac w x)] (k : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    iteratedDeriv k (cauchyTransform (countableWeightedDirac w x)) z
      = ((Nat.factorial k : ℕ) : ℂ) * ∑' n, (w n : ℂ) * (((x n : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) := by
  rw [iteratedDeriv_cauchyTransform _ k hz, cauchyKernelMoment_countableWeightedDirac hw k hz]

/-- **The jet packet of a discrete Cauchy transform, in column coordinates.**  At a finite family of
nodes and orders the packet is the mass-weighted sum of the controllability columns, each entry
rescaled by the factorial of its order. -/
theorem cauchyJetPacket_countableWeightedDirac {ι : Type*} [Fintype ι] {w x : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) [IsFiniteMeasure (countableWeightedDirac w x)] (nodes : ι → ℂ)
    (hnodes : ∀ i, (nodes i).im ≠ 0) (ord : ι → ℕ) (s : (i : ι) × Fin (ord i)) :
    iteratedDeriv (s.2 : ℕ) (cauchyTransform (countableWeightedDirac w x)) (nodes s.1)
      = ((Nat.factorial (s.2 : ℕ) : ℕ) : ℂ)
        * ∑' n, (w n : ℂ) * cauchyJetColumn nodes ord (fun n => ((x n : ℝ) : ℂ)) n s := by
  rw [iteratedDeriv_cauchyTransform_countableWeightedDirac hw _ (hnodes s.1)]
  rfl

/-! ## The reach of a multiplicative mass perturbation -/

/-- The Cauchy-jet column of one atom, rescaled by the order factorials and by the atom's mass: the
vector along which a multiplicative perturbation of that mass moves the jet packet. -/
def massJetColumn {ι : Type*} (nodes : ι → ℂ) (ord : ι → ℕ) (x w : ℕ → ℝ) (n : ℕ) :
    (Σ i, Fin (ord i)) → ℂ :=
  fun t => (w n : ℂ) * (((Nat.factorial (t.2 : ℕ) : ℕ) : ℂ)
    * cauchyJetColumn nodes ord (fun m => ((x m : ℝ) : ℂ)) n t)

theorem massJetColumn_eq_smul {ι : Type*} (nodes : ι → ℂ) (ord : ι → ℕ) (x w : ℕ → ℝ) (n : ℕ) :
    massJetColumn nodes ord x w n
      = w n • fun t : (Σ i, Fin (ord i)) => ((Nat.factorial (t.2 : ℕ) : ℕ) : ℂ)
        * cauchyJetColumn nodes ord (fun m => ((x m : ℝ) : ℂ)) n t := by
  funext t
  rw [massJetColumn, Pi.smul_apply, Complex.real_smul]

/-- **The mass columns span the jet packet space.**  Rescaling by the order factorials and by the
nonzero masses preserves the spanning property of the controllability columns. -/
theorem span_range_massJetColumn_eq_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodes : Function.Injective nodes) (hupper : ∀ i, 0 < (nodes i).im)
    (ord : ι → ℕ) (x : ℕ → ℝ) (hx : Function.Injective x) (w : ℕ → ℝ) (hw : ∀ n, w n ≠ 0) :
    Submodule.span ℝ (Set.range (massJetColumn nodes ord x w)) = ⊤ := by
  have hcol := span_range_cauchyJetColumn_eq_top nodes hnodes hupper ord x hx
  have hfact : ∀ t : (Σ i, Fin (ord i)), ((Nat.factorial (t.2 : ℕ) : ℕ) : ℂ) ≠ 0 := by
    intro t
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hdiag := span_range_diagScale_eq_top _ hfact _ hcol
  have hsmul := span_range_smul_eq_top _ w hw hdiag
  have heq : massJetColumn nodes ord x w
      = fun n => w n • fun t : (Σ i, Fin (ord i)) => ((Nat.factorial (t.2 : ℕ) : ℕ) : ℂ)
        * cauchyJetColumn nodes ord (fun m => ((x m : ℝ) : ℂ)) n t := by
    funext n
    exact massJetColumn_eq_smul nodes ord x w n
  rw [heq]
  exact hsmul

/-- **Small multiplicative mass perturbations reach a neighbourhood of the discrete jet packet.**
Finitely many atoms suffice, and their masses move only by factors arbitrarily close to one. -/
theorem exists_discreteCauchyJet_expBox_reach {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodes : Function.Injective nodes) (hupper : ∀ i, 0 < (nodes i).im)
    (ord : ι → ℕ) (x : ℕ → ℝ) (hx : Function.Injective x) (w : ℕ → ℝ) (hw : ∀ n, w n ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K : ℕ) (a : Fin K → ℕ), Function.Injective a ∧
      {y : (Σ i, Fin (ord i)) → ℂ | ∃ s : Fin K → ℝ, (∀ k, |s k| < δ) ∧
          ∑ k, (Real.exp (s k) - 1) • massJetColumn nodes ord x w (a k) = y}
        ∈ nhds (0 : (Σ i, Fin (ord i)) → ℂ) := by
  haveI : Fintype ((i : ι) × Fin (ord i)) := inferInstance
  exact exists_expBox_reach_of_span_range _
    (span_range_massJetColumn_eq_top nodes hnodes hupper ord x hx w hw) hδ

/-! ## Rescaling finitely many masses -/

/-- The weights obtained by rescaling finitely many masses by exponential factors. -/
def perturbedWeight {K : ℕ} (a : Fin K → ℕ) (s : Fin K → ℝ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  w n * Real.exp (∑ k, if a k = n then s k else 0)

theorem perturbedWeight_of_notMem {K : ℕ} {a : Fin K → ℕ} (s : Fin K → ℝ) (w : ℕ → ℝ) {n : ℕ}
    (hn : ∀ k, a k ≠ n) : perturbedWeight a s w n = w n := by
  rw [perturbedWeight]
  have hzero : (∑ k, if a k = n then s k else 0) = 0 :=
    Finset.sum_eq_zero fun k _ => if_neg (hn k)
  rw [hzero, Real.exp_zero, mul_one]

theorem perturbedWeight_apply {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a)
    (s : Fin K → ℝ) (w : ℕ → ℝ) (k : Fin K) :
    perturbedWeight a s w (a k) = w (a k) * Real.exp (s k) := by
  rw [perturbedWeight]
  congr 2
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
  · intro b _ hb
    exact if_neg fun h => hb (ha h)
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- **Rescaling finitely many masses moves a weighted sum by the corresponding finite
combination.** -/
theorem tsum_perturbedWeight_sub {σ : Type*} {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a)
    (s : Fin K → ℝ) (w : ℕ → ℝ) (col : ℕ → σ → ℂ) (t : σ)
    (hs : Summable fun n => ((w n : ℝ) : ℂ) * col n t)
    (hs' : Summable fun n => ((perturbedWeight a s w n : ℝ) : ℂ) * col n t) :
    (∑' n, ((perturbedWeight a s w n : ℝ) : ℂ) * col n t)
        - ∑' n, ((w n : ℝ) : ℂ) * col n t
      = ∑ k, ((Real.exp (s k) - 1 : ℝ) : ℂ) * (((w (a k) : ℝ) : ℂ) * col (a k) t) := by
  classical
  rw [← hs'.tsum_sub hs]
  have hvanish : ∀ n ∉ Finset.univ.image a,
      ((perturbedWeight a s w n : ℝ) : ℂ) * col n t - ((w n : ℝ) : ℂ) * col n t = 0 := by
    intro n hn
    have hne : ∀ k, a k ≠ n := by
      intro k hk
      exact hn (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩)
    rw [perturbedWeight_of_notMem s w hne, sub_self]
  rw [tsum_eq_sum hvanish, Finset.sum_image (fun k _ l _ h => ha h)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [perturbedWeight_apply ha s w k]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
