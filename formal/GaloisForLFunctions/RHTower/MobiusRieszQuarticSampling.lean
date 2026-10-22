import GaloisForLFunctions.RHTower.Suzuki.SuzukiObserverJetTerminalLayer
import GaloisForLFunctions.HTGeometry.SecondCenteredModularAbel
import GaloisForLFunctions.RHTower.PsiRemainderSignChange

/-!
# One-sided fourth-power sampling of the literal Abel moment

The completed arithmetic Riesz moment has a one-sided second-difference bound
on every block `[n^4, (n+1)^4]`. The von-Mangoldt contribution is nonnegative;
the remaining clock and polar terms are bounded by `C/n^2`.

A discrete quadratic barrier controls the moment between the two endpoints.
Since the block length is at most `15 n^3`, the interpolation error is at most
`(225/8) C M`, at the required linear aperture scale. Consequently RH is
equivalent to eventual upper boundedness of the normalized moment restricted
to fourth-power apertures. The arithmetic upper bound on those samples is
still an unproved premise; this module does not prove RH.
-/

open Set Filter Topology
open scoped BigOperators
noncomputable section


namespace GaloisForLFunctions.HTGeometry

theorem discrete_convex_le_endpoint_max (f : ℕ → ℝ) (N : ℕ)
    (hconv : ∀ k : ℕ, k + 2 ≤ N → 2 * f (k + 1) ≤ f k + f (k + 2)) :
    ∀ j : ℕ, j ≤ N → f j ≤ max (f 0) (f N) := by
  induction N with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    simp [this]
  | succ N ih =>
    cases N with
    | zero =>
      intro j hj
      interval_cases j <;> simp
    | succ n =>
      have hprev := ih (fun k hk => hconv k (by omega))
      have hmiddle : f (n + 1) ≤ max (f 0) (f (n + 2)) := by
        by_cases hzero : f (n + 1) ≤ f 0
        · exact hzero.trans (le_max_left _ _)
        · have hn := hprev n (by omega)
          have hm : max (f 0) (f (n + 1)) = f (n + 1) := max_eq_right (le_of_not_ge hzero)
          rw [hm] at hn
          have hc := hconv n (by omega)
          have hstep : f (n + 1) ≤ f (n + 2) := by linarith
          exact hstep.trans (le_max_right _ _)
      intro j hj
      by_cases hlast : j = n + 2
      · subst j
        exact le_max_right _ _
      · have hjprev : j ≤ n + 1 := by omega
        exact (hprev j hjprev).trans (max_le (le_max_left _ _) hmiddle)

theorem discrete_semiconvex_le_endpoint_max (f : ℕ → ℝ) (N : ℕ)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ k : ℕ, k + 2 ≤ N →
      -(K) ≤ f (k + 2) - 2 * f (k + 1) + f k)
    {j : ℕ} (hj : j ≤ N) :
    f j ≤ max (f 0) (f N) + K * (N : ℝ) ^ 2 / 8 := by
  let g : ℕ → ℝ := fun k => f k - (K / 2) * (k : ℝ) * ((N : ℝ) - (k : ℝ))
  have hg : ∀ k : ℕ, k + 2 ≤ N → 2 * g (k + 1) ≤ g k + g (k + 2) := by
    intro k hk
    have hc := hcurv k hk
    dsimp [g]
    push_cast
    nlinarith
  have hmax := discrete_convex_le_endpoint_max g N hg j hj
  have hzero : g 0 = f 0 := by simp [g]
  have hend : g N = f N := by simp [g]
  rw [hzero, hend] at hmax
  dsimp [g] at hmax
  have hquad : (j : ℝ) * ((N : ℝ) - (j : ℝ)) ≤ (N : ℝ) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((j : ℝ) - (N : ℝ) / 2)]
  have hmul := mul_le_mul_of_nonneg_left hquad (div_nonneg hK (by norm_num : (0 : ℝ) ≤ 2))
  nlinarith

theorem exists_nat_quartic_bracket {M : ℕ} (hM : 1 ≤ M) :
    ∃ n : ℕ, 1 ≤ n ∧ n ^ 4 ≤ M ∧ M ≤ (n + 1) ^ 4 := by
  induction M, hM using Nat.le_induction with
  | base => exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  | succ M hM ih =>
    obtain ⟨n, hn, hlo, hhi⟩ := ih
    by_cases hnext : M + 1 ≤ (n + 1) ^ 4
    · exact ⟨n, hn, by omega, hnext⟩
    · refine ⟨n + 1, by omega, by omega, ?_⟩
      have hp : (n + 1) ^ 4 < (n + 2) ^ 4 := by gcongr; omega
      simpa only [Nat.add_assoc] using (show M + 1 ≤ (n + 2) ^ 4 by omega)

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower _root_.HTGeometry GaloisForLFunctions.HTGeometry

def mobiusRieszQuarticCurvatureConstant : ℝ :=
  4 * completedSourceObserverJetChargeConstant + 1

theorem mobiusRieszQuarticCurvatureConstant_nonneg :
    0 ≤ mobiusRieszQuarticCurvatureConstant := by
  have := completedSourceObserverJetChargeConstant_nonneg
  unfold mobiusRieszQuarticCurvatureConstant
  positivity

theorem mobiusDivisorSquareRootAbel_secondDifference_quartic_lower
    {n k : ℕ} (hn : 1 ≤ n) (hlo : n ^ 4 ≤ k) (hhi : k ≤ (n + 1) ^ 4) :
    -(mobiusRieszQuarticCurvatureConstant / (n : ℝ) ^ 2) ≤
      mobiusDivisorSquareRootAbelMoment (k + 2) -
        2 * mobiusDivisorSquareRootAbelMoment (k + 1) +
          mobiusDivisorSquareRootAbelMoment k := by
  let w := halfOrderAbelStep 0
  let E : ℕ → ℝ := fun j => psiRemainder j + 2 * Real.eulerMascheroniConstant
  let A := completedSourceObserverJetChargeConstant
  have hA : 0 ≤ A := completedSourceObserverJetChargeConstant_nonneg
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hnp : 0 < (n : ℝ) ^ 2 := by positivity
  have hnNat : 0 < n := by omega
  have hk : 1 ≤ k := by
    have : 1 ≤ n ^ 4 := by
      calc
        1 = (1 : ℕ) ^ 4 := by norm_num
        _ ≤ n ^ 4 := by gcongr
    omega
  have hupper : (n + 1) ^ 4 ≤ 16 * n ^ 4 := by
    calc
      _ ≤ (2 * n) ^ 4 := by gcongr; omega
      _ = _ := by ring
  have hbase : n ^ 2 * n ^ 2 = n ^ 4 := by ring
  have hstepBase : w (n ^ 4) ≤ 1 / (n : ℝ) ^ 2 := by
    have h := halfOrderAbelStep_square_initial (n ^ 2)
    have h' : (n : ℝ) ^ 2 * w (n ^ 4) ≤ 1 / 2 := by
      simpa only [w, halfOrderAbelStep, hbase, Nat.add_zero, Nat.zero_add, Nat.cast_pow] using h
    apply (le_div_iff₀ hnp).mpr
    nlinarith
  have hgapBase : w (n ^ 4) - w (n ^ 4 + 1) ≤ 1 / (4 * (n : ℝ) ^ 6) := by
    have h := halfOrderAbelStep_square_gap_le (d := n ^ 2) (by positivity)
    simpa only [w, halfOrderAbelStep, hbase, Nat.add_zero, Nat.zero_add,
      Nat.cast_pow, ← pow_mul] using h
  have hstep : w (k + 1) ≤ 1 / (n : ℝ) ^ 2 :=
    (halfOrderAbelStep_antitone 0 (by omega : n ^ 4 ≤ k + 1)).trans hstepBase
  have hgap : w k - w (k + 1) ≤ 1 / (4 * (n : ℝ) ^ 6) :=
    (halfOrderAbelStep_gap_antitone 0 hlo).trans hgapBase
  have hgap0 : 0 ≤ w k - w (k + 1) :=
    sub_nonneg.mpr (halfOrderAbelStep_antitone 0 (by omega : k ≤ k + 1))
  have hE : E k ≤ 16 * A * (n : ℝ) ^ 4 := by
    have hR := abs_psiRemainder_le k
    have hkle : (k : ℝ) ≤ 16 * (n : ℝ) ^ 4 := by exact_mod_cast hhi.trans hupper
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hgamma := le_abs_self (2 * Real.eulerMascheroniConstant)
    have hgprod := mul_le_mul_of_nonneg_left hkr (abs_nonneg (2 * Real.eulerMascheroniConstant))
    have he : E k ≤ A * (k : ℝ) := by
      dsimp [E, A, completedSourceObserverJetChargeConstant]
      nlinarith [le_abs_self (psiRemainder k)]
    exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hkle hA])
  have hgapE : (w k - w (k + 1)) * E k ≤ 4 * A / (n : ℝ) ^ 2 := by
    calc
      _ ≤ (w k - w (k + 1)) * (16 * A * (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hE hgap0
      _ ≤ (1 / (4 * (n : ℝ) ^ 6)) * (16 * A * (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right hgap (by positivity)
      _ = _ := by field_simp; ring
  have h0 : mobiusDivisorSquareRootAbelMoment (k + 1) -
      mobiusDivisorSquareRootAbelMoment k = w k * E k := by
    simpa only [w, E, halfOrderAbelStep, Nat.zero_add] using
      mobiusDivisorSquareRootAbelMoment_succ_sub hk
  have h1 : mobiusDivisorSquareRootAbelMoment (k + 2) -
      mobiusDivisorSquareRootAbelMoment (k + 1) = w (k + 1) * E (k + 1) := by
    simpa only [w, E, halfOrderAbelStep, Nat.zero_add] using
      mobiusDivisorSquareRootAbelMoment_succ_sub (M := k + 1) (by omega)
  have he : E (k + 1) - E k = ArithmeticFunction.vonMangoldt (k + 1) - 1 := by
    dsimp [E]
    linarith [psiRemainder_succ_sub k]
  have hnonneg := mul_nonneg (halfOrderAbelStep_nonneg 0 (k + 1))
    (ArithmeticFunction.vonMangoldt_nonneg (n := k + 1))
  have hid : mobiusDivisorSquareRootAbelMoment (k + 2) -
      2 * mobiusDivisorSquareRootAbelMoment (k + 1) +
        mobiusDivisorSquareRootAbelMoment k =
      w (k + 1) * ArithmeticFunction.vonMangoldt (k + 1) - w (k + 1) -
        (w k - w (k + 1)) * E k := by
    have he' : E (k + 1) = E k + ArithmeticFunction.vonMangoldt (k + 1) - 1 := by linarith
    rw [he'] at h1
    nlinarith only [h0, h1]
  rw [hid]
  change -((4 * A + 1) / (n : ℝ) ^ 2) ≤ _
  change 0 ≤ w (k + 1) * ArithmeticFunction.vonMangoldt (k + 1) at hnonneg
  calc
    -((4 * A + 1) / (n : ℝ) ^ 2) = -(1 / (n : ℝ) ^ 2) - 4 * A / (n : ℝ) ^ 2 := by ring
    _ ≤ -w (k + 1) - (w k - w (k + 1)) * E k := sub_le_sub (neg_le_neg hstep) hgapE
    _ ≤ _ := by linarith only [hnonneg]

theorem mobiusDivisorSquareRootAbelMoment_le_quartic_endpoints
    {n M : ℕ} (hn : 1 ≤ n) (hlo : n ^ 4 ≤ M) (hhi : M ≤ (n + 1) ^ 4) :
    mobiusDivisorSquareRootAbelMoment M ≤
      max (mobiusDivisorSquareRootAbelMoment (n ^ 4))
        (mobiusDivisorSquareRootAbelMoment ((n + 1) ^ 4)) +
          (225 / 8 : ℝ) * mobiusRieszQuarticCurvatureConstant * (M : ℝ) := by
  have hab : n ^ 4 ≤ (n + 1) ^ 4 := hlo.trans hhi
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hC := mobiusRieszQuarticCurvatureConstant_nonneg
  have hK : 0 ≤ mobiusRieszQuarticCurvatureConstant / (n : ℝ) ^ 2 := by positivity
  have hcurv (k : ℕ) (hk : k + 2 ≤ (n + 1) ^ 4 - n ^ 4) :
      -(mobiusRieszQuarticCurvatureConstant / (n : ℝ) ^ 2) ≤
        mobiusDivisorSquareRootAbelMoment (n ^ 4 + (k + 2)) -
          2 * mobiusDivisorSquareRootAbelMoment (n ^ 4 + (k + 1)) +
            mobiusDivisorSquareRootAbelMoment (n ^ 4 + k) := by
    rw [← Nat.add_assoc (n ^ 4) k 2, ← Nat.add_assoc (n ^ 4) k 1]
    exact mobiusDivisorSquareRootAbel_secondDifference_quartic_lower hn
      (k := n ^ 4 + k) (by omega) (by omega)
  have hi := discrete_semiconvex_le_endpoint_max
    (fun k => mobiusDivisorSquareRootAbelMoment (n ^ 4 + k))
    ((n + 1) ^ 4 - n ^ 4) hK hcurv (j := M - n ^ 4) (by omega)
  simp only [Nat.add_zero,
    show n ^ 4 + (M - n ^ 4) = M by omega,
    show n ^ 4 + ((n + 1) ^ 4 - n ^ 4) = (n + 1) ^ 4 by omega] at hi
  have hgap : (((n + 1) ^ 4 - n ^ 4 : ℕ) : ℝ) ≤ 15 * (n : ℝ) ^ 3 := by
    rw [Nat.cast_sub hab]
    push_cast
    have hn1 := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sub_nonneg.mpr hnR)
    have hn2 := mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hnR)
    nlinarith
  have hgapSq : (((n + 1) ^ 4 - n ^ 4 : ℕ) : ℝ) ^ 2 ≤
      (15 * (n : ℝ) ^ 3) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hgap
  have herr : (mobiusRieszQuarticCurvatureConstant / (n : ℝ) ^ 2) *
      (((n + 1) ^ 4 - n ^ 4 : ℕ) : ℝ) ^ 2 / 8 ≤
      (225 / 8 : ℝ) * mobiusRieszQuarticCurvatureConstant * (M : ℝ) := by
    calc
      _ ≤ (mobiusRieszQuarticCurvatureConstant / (n : ℝ) ^ 2) *
          (15 * (n : ℝ) ^ 3) ^ 2 / 8 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgapSq hK) (by norm_num)
      _ = (225 / 8 : ℝ) * mobiusRieszQuarticCurvatureConstant * (n : ℝ) ^ 4 := by
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hlo) (by positivity)
  exact hi.trans (add_le_add le_rfl herr)

theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbel_quartic_eventually_boundedAbove :
    RiemannHypothesis ↔ ∃ (B : ℝ) (N₀ : ℕ), ∀ n : ℕ, max 2 N₀ ≤ n →
      mobiusDivisorSquareRootAbelMoment (n ^ 4) / (n ^ 4 : ℕ) ≤ B := by
  constructor
  · intro hRH
    obtain ⟨B, hB⟩ := riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedAbove.mp hRH
    refine ⟨B, 2, fun n hn => hB (n ^ 4) ?_⟩
    have hn2 : 2 ≤ n := by omega
    calc
      2 ≤ (2 : ℕ) ^ 4 := by norm_num
      _ ≤ n ^ 4 := by gcongr
  · rintro ⟨B, N₀, hB⟩
    let T := max 2 N₀
    let C := max B 0
    have hC : 0 ≤ C := le_max_right _ _
    have hpoint (n : ℕ) (hn : T ≤ n) :
        mobiusDivisorSquareRootAbelMoment (n ^ 4) ≤ C * (n ^ 4 : ℕ) := by
      have hn0 : 0 < n := by dsimp [T] at hn; omega
      have hp : 0 < (n ^ 4 : ℕ) := by positivity
      have hpR : (0 : ℝ) < (n ^ 4 : ℕ) := by exact_mod_cast hp
      apply (div_le_iff₀ hpR).mp
      exact (hB n hn).trans (le_max_left _ _)
    apply riemannHypothesis_iff_mobiusDivisorSquareRootAbel_eventually_boundedAbove.mpr
    refine ⟨16 * C + (225 / 8 : ℝ) * mobiusRieszQuarticCurvatureConstant,
      (T + 1) ^ 4, ?_⟩
    intro M hM
    have hM2 : 2 ≤ M := by omega
    have hcut : (T + 1) ^ 4 ≤ M := by omega
    obtain ⟨n, hn, hlo, hhi⟩ := exists_nat_quartic_bracket (M := M) (by omega)
    have hnT : T ≤ n := by
      by_contra hnot
      have hsmall : (n + 1) ^ 4 ≤ T ^ 4 := by gcongr; omega
      have hstrict : T ^ 4 < (T + 1) ^ 4 := by gcongr; omega
      omega
    have hupper : (n + 1) ^ 4 ≤ 16 * n ^ 4 := by
      calc
        _ ≤ (2 * n) ^ 4 := by gcongr; omega
        _ = _ := by ring
    have hendpoint : max (mobiusDivisorSquareRootAbelMoment (n ^ 4))
        (mobiusDivisorSquareRootAbelMoment ((n + 1) ^ 4)) ≤ 16 * C * (M : ℝ) := by
      apply max_le
      · have hp := hpoint n hnT
        have hM0 : (0 : ℝ) ≤ M := by positivity
        have hloR : (n ^ 4 : ℕ) ≤ (M : ℝ) := by exact_mod_cast hlo
        nlinarith [mul_le_mul_of_nonneg_left hloR hC, mul_nonneg hC hM0]
      · have hp := hpoint (n + 1) (by omega)
        have hu : ((n + 1) ^ 4 : ℕ) ≤ 16 * (M : ℝ) := by
          exact_mod_cast (hupper.trans (Nat.mul_le_mul_left 16 hlo))
        nlinarith [mul_le_mul_of_nonneg_left hu hC]
    have hbridge := mobiusDivisorSquareRootAbelMoment_le_quartic_endpoints hn hlo hhi
    apply (div_le_iff₀ (show (0 : ℝ) < M by exact_mod_cast (show 0 < M by omega))).mpr
    nlinarith

end GaloisForLFunctions.RHTower
