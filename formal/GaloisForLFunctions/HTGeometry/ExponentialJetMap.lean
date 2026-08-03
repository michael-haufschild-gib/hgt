import GaloisForLFunctions.HTGeometry.TriangularSolvability
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The jet map of an exponential

The derivatives of `exp ∘ f` at a point are determined by the derivatives of `f` there, through the
Leibniz recursion coming from `(exp ∘ f)' = (exp ∘ f) · f'`.  The resulting map on jet packets is
triangular: past the term `exp(y_0) y_(k+1)` the `k+1`-st entry involves only lower jets.

Its diagonal `exp(y_0)` never vanishes, so the triangular system is always solvable, and the solution
depends continuously on the target.  The jet map is therefore a homeomorphism onto the packets with
nonvanishing zeroth entry, once a branch of the logarithm is fixed for that entry.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The scalar Leibniz recursion for the jets of an exponential: `expJetScalar y k` is the `k`-th
derivative of `exp ∘ f` expressed in the jets `y j = f^(j)`. -/
def expJetScalar (y : ℕ → ℂ) : ℕ → ℂ
  | 0 => Complex.exp (y 0)
  | (k + 1) =>
      ∑ i ∈ (Finset.range (k + 1)).attach,
        ((k.choose (i : ℕ) : ℕ) : ℂ) * expJetScalar y (i : ℕ) * y (k - (i : ℕ) + 1)
  decreasing_by
    have hi := Finset.mem_range.mp i.2
    omega

theorem expJetScalar_zero (y : ℕ → ℂ) : expJetScalar y 0 = Complex.exp (y 0) := by
  rw [expJetScalar]

theorem expJetScalar_succ (y : ℕ → ℂ) (k : ℕ) :
    expJetScalar y (k + 1)
      = ∑ i ∈ Finset.range (k + 1),
          ((k.choose i : ℕ) : ℂ) * expJetScalar y i * y (k - i + 1) := by
  rw [expJetScalar]
  exact Finset.sum_attach (Finset.range (k + 1))
    fun i => ((k.choose i : ℕ) : ℂ) * expJetScalar y i * y (k - i + 1)

/-- The `k`-th exponential jet depends only on the jets up to order `k`. -/
theorem expJetScalar_congr (y y' : ℕ → ℂ) :
    ∀ k, (∀ j, j ≤ k → y j = y' j) → expJetScalar y k = expJetScalar y' k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro h
      cases k with
      | zero =>
          rw [expJetScalar_zero, expJetScalar_zero, h 0 (le_refl 0)]
      | succ k =>
          rw [expJetScalar_succ, expJetScalar_succ]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [ih i (by omega) fun j hj => h j (by omega),
            h (k - i + 1) (by omega)]

/-- **The exponential jet map is triangular.**  Past the diagonal term `exp(y_0) y_(k+1)` the
`k+1`-st jet depends only on the jets of order at most `k`. -/
theorem expJetScalar_succ_sub_diagonal (k : ℕ) (y y' : ℕ → ℂ)
    (h : ∀ j, j ≤ k → y j = y' j) :
    expJetScalar y (k + 1) - Complex.exp (y 0) * y (k + 1)
      = expJetScalar y' (k + 1) - Complex.exp (y' 0) * y' (k + 1) := by
  have hexp : ∀ z : ℕ → ℂ, expJetScalar z (k + 1)
      = Complex.exp (z 0) * z (k + 1)
        + ∑ i ∈ Finset.range k,
            (((k.choose (i + 1) : ℕ)) : ℂ) * expJetScalar z (i + 1) * z (k - (i + 1) + 1) := by
    intro z
    rw [expJetScalar_succ, Finset.sum_range_succ']
    have h0 : ((k.choose 0 : ℕ) : ℂ) * expJetScalar z 0 * z (k - 0 + 1)
        = Complex.exp (z 0) * z (k + 1) := by
      rw [Nat.choose_zero_right, Nat.sub_zero, expJetScalar_zero]
      norm_num
    rw [h0]
    ring
  rw [hexp y, hexp y', h 0 (Nat.zero_le k)]
  have hmid : (∑ i ∈ Finset.range k,
        (((k.choose (i + 1) : ℕ)) : ℂ) * expJetScalar y (i + 1) * y (k - (i + 1) + 1))
      = ∑ i ∈ Finset.range k,
        (((k.choose (i + 1) : ℕ)) : ℂ) * expJetScalar y' (i + 1) * y' (k - (i + 1) + 1) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [expJetScalar_congr y y' (i + 1) fun j hj => h j (by omega),
      h (k - (i + 1) + 1) (by omega)]
  rw [hmid]
  ring

/-! ## The jet map computes the derivatives of a composite -/

/-- **The recursion computes the derivatives of an exponential.** -/
theorem expJetScalar_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℂ (⊤ : ℕ∞) f U) {z : ℂ} (hz : z ∈ U) (k : ℕ) :
    expJetScalar (fun j => iteratedDeriv j f z) k
      = iteratedDeriv k (fun w => Complex.exp (f w)) z := by
  induction k using Nat.strong_induction_on generalizing z with
  | _ k ih =>
      cases k with
      | zero =>
          rw [expJetScalar_zero]
          simp
      | succ k =>
          have hderiv : ContDiffOn ℂ (⊤ : ℕ∞) (deriv f) U :=
            hf.deriv_of_isOpen hU (by simp)
          have hcomp : ContDiffOn ℂ (⊤ : ℕ∞) (fun w => Complex.exp (f w)) U := by
            exact Complex.contDiff_exp.comp_contDiffOn hf
          have heq : (fun w => deriv (fun v => Complex.exp (f v)) w)
              =ᶠ[𝓝 z] fun w => Complex.exp (f w) * deriv f w := by
            filter_upwards [hU.mem_nhds hz] with w hw
            have hfw : DifferentiableAt ℂ f w :=
              (hf.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)
            exact (Complex.hasDerivAt_exp (f w)).comp w hfw.hasDerivAt |>.deriv
          rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq k heq]
          have hexpc : ∀ w ∈ U, ContDiffAt ℂ ((k : ℕ) : ℕ∞) (fun v => Complex.exp (f v)) w :=
            fun w hw => (hcomp.contDiffAt (hU.mem_nhds hw)).of_le
              (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
          have hdc : ∀ w ∈ U, ContDiffAt ℂ ((k : ℕ) : ℕ∞) (deriv f) w :=
            fun w hw => (hderiv.contDiffAt (hU.mem_nhds hw)).of_le
              (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
          rw [iteratedDeriv_fun_mul (hexpc z hz) (hdc z hz), expJetScalar_succ]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [ih i (by omega) hz]
          congr 1
          rw [← iteratedDeriv_succ']

/-! ## Solving the jet system -/

/-- **The exponential jet map is onto every packet whose zeroth entry has a logarithm.**  The
zeroth equation fixes the branch, and the remaining triangular system has nonvanishing diagonal
`exp(y_0)`. -/
theorem exists_expJetScalar_eq {y₀ : ℂ} {w : ℕ → ℂ} (hw : Complex.exp y₀ = w 0) :
    ∃ y : ℕ → ℂ, y 0 = y₀ ∧ ∀ k, expJetScalar y k = w k := by
  classical
  have hd : Complex.exp y₀ ≠ 0 := Complex.exp_ne_zero y₀
  set ext : (ℕ → ℂ) → ℕ → ℂ := fun u j => if j = 0 then y₀ else u (j - 1) with hext
  have hext0 : ∀ u, ext u 0 = y₀ := by intro u; simp [hext]
  have hextsucc : ∀ (u : ℕ → ℂ) (j : ℕ), ext u (j + 1) = u j := by intro u j; simp [hext]
  have hL : ∀ (k : ℕ) (u u' : ℕ → ℂ), (∀ j, j < k → u j = u' j) →
      expJetScalar (ext u) (k + 1) - Complex.exp y₀ * u k
        = expJetScalar (ext u') (k + 1) - Complex.exp y₀ * u' k := by
    intro k u u' hagree
    have hcoord : ∀ j, j ≤ k → ext u j = ext u' j := by
      intro j hj
      cases j with
      | zero => rw [hext0, hext0]
      | succ l => rw [hextsucc, hextsucc, hagree l (by omega)]
    have hstep := expJetScalar_succ_sub_diagonal k (ext u) (ext u') hcoord
    rwa [hext0, hext0, hextsucc, hextsucc] at hstep
  obtain ⟨u, hu⟩ := exists_triangular_solution hd
    (fun k u => expJetScalar (ext u) (k + 1) - Complex.exp y₀ * u k) hL
    (fun k => w (k + 1))
  refine ⟨ext u, hext0 u, ?_⟩
  intro k
  cases k with
  | zero =>
      rw [expJetScalar_zero, hext0]
      exact hw
  | succ k =>
      have hk := hu k
      linear_combination hk

end

end GaloisForLFunctions.HTGeometry
