import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.GammaShiftConfluentAnnihilator

/-!
# Exact finite Gamma-jet annihilators

The prescribed-root polynomial from `GammaShiftConfluentAnnihilator` is now connected to the
analytic Gamma function.  Away from the Gamma poles, its ascending-Pochhammer coordinates define a
monic consecutive-shift operator that annihilates every requested translated Gamma jet.
-/

open scoped BigOperators Topology

namespace GaloisForLFunctions

open Filter Polynomial

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The canonical coefficient of the `k`-th consecutive shift. -/
def gammaJetAnnihilatorCoeff (s : ℂ) (shift : ι → ℂ) (mult : ι → ℕ) (k : ℕ) : ℂ :=
  ascPochhammerCoeff ℂ (gammaJetRootPolynomial ℂ s shift mult) k

/-- The canonical finite consecutive-shift operator evaluated at `s`. -/
def gammaJetAnnihilator (s : ℂ) (shift : ι → ℂ) (mult : ι → ℕ) (f : ℂ → ℂ) : ℂ :=
  ∑ k ∈ Finset.range (gammaJetOrder mult + 1),
    gammaJetAnnihilatorCoeff s shift mult k * f (s + k)

/-- The top shift coefficient is one. -/
theorem gammaJetAnnihilatorCoeff_top (s : ℂ) (shift : ι → ℂ) (mult : ι → ℕ) :
    gammaJetAnnihilatorCoeff s shift mult (gammaJetOrder mult) = 1 := by
  exact gammaJetRootPolynomial_topCoeff ℂ s shift mult

/-- Equation (4): monic top shift plus the lower consecutive shifts. -/
theorem gammaJetAnnihilator_eq_monic (s : ℂ) (shift : ι → ℂ) (mult : ι → ℕ)
    (f : ℂ → ℂ) :
    gammaJetAnnihilator s shift mult f =
      f (s + gammaJetOrder mult) +
        ∑ k ∈ Finset.range (gammaJetOrder mult),
          gammaJetAnnihilatorCoeff s shift mult k * f (s + k) := by
  rw [gammaJetAnnihilator, Finset.sum_range_succ, gammaJetAnnihilatorCoeff_top,
    one_mul, add_comm]

/-- A finite initial segment of the translated argument stays away from zero in a neighborhood of
an off-pole point. -/
theorem eventually_gamma_shift_regular {x : ℂ}
    (hx : ∀ n : ℕ, x ≠ -(n : ℂ)) (N : ℕ) :
    ∀ᶠ z in 𝓝 x, ∀ t < N, z + (t : ℂ) ≠ 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hxN : x + (N : ℂ) ≠ 0 := by
        intro hzero
        apply hx N
        linear_combination hzero
      have hN : ∀ᶠ z in 𝓝 x, z + (N : ℂ) ≠ 0 :=
        (continuousAt_id.add continuousAt_const).eventually_ne hxN
      filter_upwards [ih, hN] with z hz hzN
      intro t ht
      by_cases hlt : t < N
      · exact hz t hlt
      · have htN : t = N := Nat.le_antisymm (Nat.le_of_lt_succ ht) (Nat.le_of_not_gt hlt)
        simpa [htN] using hzN

/-- Locally, the shift sum is exactly the prescribed-root polynomial times Gamma. -/
theorem gamma_shift_sum_eventuallyEq_root_mul
    (s : ℂ) (shift : ι → ℂ) (mult : ι → ℕ) (i : ι)
    (hpole : ∀ n : ℕ, s + shift i ≠ -(n : ℂ)) :
    (fun z => ∑ k ∈ Finset.range (gammaJetOrder mult + 1),
        gammaJetAnnihilatorCoeff s shift mult k * Complex.Gamma (z + k))
      =ᶠ[𝓝 (s + shift i)]
      (fun z => (gammaJetRootPolynomial ℂ s shift mult).eval z * Complex.Gamma z) := by
  have hreg := eventually_gamma_shift_regular hpole (gammaJetOrder mult + 1)
  filter_upwards [hreg] with z hz
  have hexp := gammaJetRootPolynomial_expansion ℂ s shift mult
  rw [show (gammaJetRootPolynomial ℂ s shift mult).eval z =
      (∑ k ∈ Finset.range (gammaJetOrder mult + 1),
        ascPochhammerCoeff ℂ (gammaJetRootPolynomial ℂ s shift mult) k •
          ascPochhammer ℂ k).eval z from congrArg (Polynomial.eval z) hexp]
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_smul, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Complex.Gamma_add_nat_eq_ascPochhammer_mul z k]
  · rw [gammaJetAnnihilatorCoeff]
    ring
  · intro t ht
    exact hz t (ht.trans (Finset.mem_range.mp hk))

/-- Equation (6): the canonical consecutive-shift sum annihilates every prescribed Gamma jet. -/
theorem gammaJetAnnihilator_iteratedDeriv_sum_eq_zero
    (s : ℂ) (shift : ι → ℂ) (mult : ι → ℕ)
    (hpole : ∀ (i : ι) (n : ℕ), s + shift i ≠ -(n : ℂ))
    (i : ι) {m : ℕ} (hm : m < mult i) :
    ∑ k ∈ Finset.range (gammaJetOrder mult + 1),
      gammaJetAnnihilatorCoeff s shift mult k *
        iteratedDeriv m Complex.Gamma (s + shift i + k) = 0 := by
  let x := s + shift i
  have heq := gamma_shift_sum_eventuallyEq_root_mul s shift mult i (hpole i)
  have hderivEq := heq.iteratedDeriv_eq m
  have hxk : ∀ k : ℕ, ∀ n : ℕ, x + (k : ℂ) ≠ -(n : ℂ) := by
    intro k n hzero
    apply hpole i (n + k)
    push_cast
    linear_combination hzero
  have hf : ∀ k ∈ Finset.range (gammaJetOrder mult + 1),
      ContDiffAt ℂ m
        (fun z => gammaJetAnnihilatorCoeff s shift mult k * Complex.Gamma (z + k)) x := by
    intro k _
    exact contDiffAt_const.mul
      ((contDiffAt_Gamma (x + k) (hxk k) m).comp x (by fun_prop))
  have hleft :
      iteratedDeriv m
        (fun z => ∑ k ∈ Finset.range (gammaJetOrder mult + 1),
          gammaJetAnnihilatorCoeff s shift mult k * Complex.Gamma (z + k)) x =
        ∑ k ∈ Finset.range (gammaJetOrder mult + 1),
          gammaJetAnnihilatorCoeff s shift mult k *
            iteratedDeriv m Complex.Gamma (x + k) := by
    rw [iteratedDeriv_fun_sum hf]
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDeriv_const_mul_field]
    have hshift := congrFun (iteratedDeriv_comp_add_const m Complex.Gamma (k : ℂ)) x
    simpa only [smul_eq_mul] using congrArg
      (fun y => gammaJetAnnihilatorCoeff s shift mult k * y) hshift
  have hright :
      iteratedDeriv m
        (fun z => (gammaJetRootPolynomial ℂ s shift mult).eval z * Complex.Gamma z) x = 0 := by
    exact iteratedDeriv_gammaJetRoot_mul_eq_zero s shift mult i Complex.Gamma hm
      (contDiffAt_Gamma x (hpole i) m)
  calc
    ∑ k ∈ Finset.range (gammaJetOrder mult + 1),
        gammaJetAnnihilatorCoeff s shift mult k *
          iteratedDeriv m Complex.Gamma (s + shift i + k) =
      iteratedDeriv m
        (fun z => ∑ k ∈ Finset.range (gammaJetOrder mult + 1),
          gammaJetAnnihilatorCoeff s shift mult k * Complex.Gamma (z + k)) x := by
        simpa only [x] using hleft.symm
    _ = iteratedDeriv m
        (fun z => (gammaJetRootPolynomial ℂ s shift mult).eval z * Complex.Gamma z) x :=
      hderivEq
    _ = 0 := hright

/-- Operator form of the exact Gamma-jet annihilation law. -/
theorem gammaJetAnnihilator_iteratedDeriv_eq_zero
    (s : ℂ) (shift : ι → ℂ) (mult : ι → ℕ)
    (hpole : ∀ (i : ι) (n : ℕ), s + shift i ≠ -(n : ℂ))
    (i : ι) {m : ℕ} (hm : m < mult i) :
    gammaJetAnnihilator s shift mult
      (fun z => iteratedDeriv m Complex.Gamma (z + shift i)) = 0 := by
  rw [gammaJetAnnihilator]
  simpa only [add_assoc, add_left_comm, add_comm] using
    gammaJetAnnihilator_iteratedDeriv_sum_eq_zero s shift mult hpole i hm

end


end GaloisForLFunctions
