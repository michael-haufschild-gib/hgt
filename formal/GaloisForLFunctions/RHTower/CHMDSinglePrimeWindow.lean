import GaloisForLFunctions.RHTower.CHMDPolarTransfer

/-!
# The single-prime-power window of the arithmetic Doob energy

The Doob energy of a compact test `v` is the archimedean Lévy form of `Θv` minus the series of
explicit-weight prime cross terms
`Σ_n 2 Λ(n) n^{-1/2} ∫ Θ(x) Θ(x + log n) v(x) v(x + log n) dx`
(the ground-state cancellation absorbs every diagonal term into the cosh mass). A test supported in
an interval of length `L` has no cross term at the prime powers `n` with `log n ≥ L`. On the
prime-blind window `L ≤ log 2` the energy is the Lévy form itself; on the single-prime-power window
`L ≤ log 3` it is the Lévy form minus the one cross term of the prime `2`, with its explicit weight
`log 2 / √2`:

`E(v) = Λ_∞(Θv) − (2 log 2 / √2) ∫ Θ(x) Θ(x + log 2) v(x) v(x + log 2) dx`.

Nonnegativity of the energy on this window is therefore exactly the domination of the prime-2
cross term by the archimedean Lévy form. The cross term is confined to the two end strips of
width `L − log 2` of the support and is bounded by `(log 2 / √2)` times the mass of `Θv` on those
strips, so a prime-free boundary coercivity of the Lévy form on the end strips implies the
domination. Under RH the domination holds for every primitive test of the window.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph

/-! ## The Lévy form and the explicit-formula form of the energy -/

/-- The archimedean Lévy form `γ(0) ∫ f² + ∫_{x>0} ω(x) ∫ (f(u) − f(u+x))² du dx`. -/
def weilLevyForm (f : ℝ → ℝ) : ℝ :=
  EF.gammaBracket 0 * (∫ x, f x ^ 2) + (NonnegativeCone.jumpEnergy f).toReal

/-- The quadratic prime pairing of `Θv` is the series of Doob prime cross terms. -/
theorem atomPairing_quad_eq_tsum_cross (v : ℝ → ℝ) :
    atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (phiDoobTest v) (phiDoobTest v)) =
      ∑' n : ℕ, ∫ x, phiDoobPrimeCross v n x := by
  unfold atomPairing
  exact tsum_congr fun n => vonMangoldtAtom_mul_crossCorr_quad_eq_integral_phiDoobPrimeCross v n

/-- **Explicit-formula form of the Doob energy**: Lévy form minus the prime cross series. -/
theorem markovEnergy_eq_levy_sub_tsum_cross {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) :
    markovEnergy (fun x => (phiDoobTest v x : ℂ)) =
      weilLevyForm (phiDoobTest v) - ∑' n : ℕ, ∫ x, phiDoobPrimeCross v n x := by
  have h1 := phiDoob_markovEnergy_levy_groundState_cancellation hv hvc
  have h2 := phiDoob_mixed_prime_pairing_eq_mixedPhiArchRe_add_phiDoobCoshMass hv hvc
  have h3 := atomPairing_mixed_sub_quad_eq_tsum_integral_phiDoobPrimeJump hv.continuous hvc
  rw [atomPairing_quad_eq_tsum_cross] at h3
  unfold weilLevyForm
  linarith

theorem sourceEnergy_compactLift_eq_levy_sub_tsum_cross (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) :
    sourceEnergy (compactLift v hv hvc) =
      weilLevyForm (phiDoobTest v) - ∑' n : ℕ, ∫ x, phiDoobPrimeCross v n x := by
  rw [sourceEnergy_compactLift, markovEnergy_eq_levy_sub_tsum_cross hv hvc]

/-! ## Windows: cross terms vanish beyond the support length -/

theorem phiDoobPrimeCross_eq_zero_of_lt_two (v : ℝ → ℝ) {n : ℕ} (hn : n < 2) (x : ℝ) :
    phiDoobPrimeCross v n x = 0 := by
  unfold phiDoobPrimeCross vonMangoldtAtom
  rw [if_neg (by omega)]
  ring

theorem phiDoobPrimeCross_eq_zero_of_window {v : ℝ → ℝ} {a L : ℝ}
    (hsupp : ∀ x ∉ Ioo a (a + L), v x = 0) {n : ℕ} (hn : L ≤ Real.log n) (x : ℝ) :
    phiDoobPrimeCross v n x = 0 := by
  unfold phiDoobPrimeCross
  by_cases hx : x ∈ Ioo a (a + L)
  · have h : v (x + Real.log n) = 0 :=
      hsupp _ fun h => by linarith [h.2, hx.1]
    rw [h]
    ring
  · rw [hsupp x hx]
    ring

theorem integral_phiDoobPrimeCross_eq_zero_of_window {v : ℝ → ℝ} {a L : ℝ}
    (hsupp : ∀ x ∉ Ioo a (a + L), v x = 0) {n : ℕ} (hn : L ≤ Real.log n) :
    ∫ x, phiDoobPrimeCross v n x = 0 := by
  have h : (fun x => phiDoobPrimeCross v n x) = fun _ => 0 :=
    funext (phiDoobPrimeCross_eq_zero_of_window hsupp hn)
  rw [h, integral_zero]

/-- On a window of length `L ≤ log m` only the prime powers `2 ≤ n < m` contribute. -/
theorem tsum_cross_eq_sum_of_window {v : ℝ → ℝ} {a L : ℝ}
    (hsupp : ∀ x ∉ Ioo a (a + L), v x = 0) {m : ℕ} (hm : 1 ≤ m) (hL : L ≤ Real.log m) :
    ∑' n : ℕ, ∫ x, phiDoobPrimeCross v n x =
      ∑ n ∈ Finset.Ico 2 m, ∫ x, phiDoobPrimeCross v n x := by
  apply tsum_eq_sum
  intro n hn
  rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hn
  rcases hn with hn | hn
  · have h : (fun x => phiDoobPrimeCross v n x) = fun _ => 0 :=
      funext (phiDoobPrimeCross_eq_zero_of_lt_two v hn)
    rw [h, integral_zero]
  · exact integral_phiDoobPrimeCross_eq_zero_of_window hsupp
      (hL.trans (Real.log_le_log (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr hn)))

/-- **Finite window.** The Doob energy on a window of length `L ≤ log m` is the Lévy form minus the
finitely many cross terms of the prime powers below `m`. -/
theorem sourceEnergy_compactLift_eq_levy_sub_finite_cross (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) {a L : ℝ} (hsupp : ∀ x ∉ Ioo a (a + L), v x = 0) {m : ℕ}
    (hm : 1 ≤ m) (hL : L ≤ Real.log m) :
    sourceEnergy (compactLift v hv hvc) =
      weilLevyForm (phiDoobTest v) - ∑ n ∈ Finset.Ico 2 m, ∫ x, phiDoobPrimeCross v n x := by
  rw [sourceEnergy_compactLift_eq_levy_sub_tsum_cross, tsum_cross_eq_sum_of_window hsupp hm hL]

/-- **Prime-blind window** (`L ≤ log 2`): the Doob energy is the archimedean Lévy form. -/
theorem sourceEnergy_compactLift_eq_levy_of_window_le_log_two (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) {a L : ℝ} (hsupp : ∀ x ∉ Ioo a (a + L), v x = 0)
    (hL : L ≤ Real.log 2) :
    sourceEnergy (compactLift v hv hvc) = weilLevyForm (phiDoobTest v) := by
  rw [sourceEnergy_compactLift_eq_levy_sub_finite_cross v hv hvc hsupp (by norm_num) hL,
    Finset.Ico_self, Finset.sum_empty, sub_zero]

/-- **Single-prime-power window** (`L ≤ log 3`): the Doob energy is the Lévy form minus the one
explicit-weight cross term of the prime `2`. -/
theorem sourceEnergy_compactLift_eq_levy_sub_cross_two (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) {a L : ℝ} (hsupp : ∀ x ∉ Ioo a (a + L), v x = 0)
    (hL : L ≤ Real.log 3) :
    sourceEnergy (compactLift v hv hvc) =
      weilLevyForm (phiDoobTest v) - ∫ x, phiDoobPrimeCross v 2 x := by
  rw [sourceEnergy_compactLift_eq_levy_sub_finite_cross v hv hvc hsupp (by norm_num) hL,
    show Finset.Ico 2 3 = {2} from Nat.Ico_succ_singleton 2, Finset.sum_singleton]

/-! ## End-strip localization of a cross term -/

/-- The cross term of the prime power `n` is bounded by `Λ(n) n^{-1/2}` times the mass of `Θv` on
the two end strips of width `L − log n` of the window. -/
theorem integral_phiDoobPrimeCross_le_strips {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) {a L : ℝ} (hsupp : ∀ x ∉ Ioo a (a + L), v x = 0) (n : ℕ) :
    ∫ x, phiDoobPrimeCross v n x ≤ vonMangoldtAtom n *
      ((∫ x in Ioo a (a + L - Real.log n), phiDoobTest v x ^ 2) +
        ∫ x in Ioo (a + Real.log n) (a + L), phiDoobTest v x ^ 2) := by
  set ℓ := Real.log n with hℓ
  set g : ℝ → ℝ := fun x => phiDoobTest v x ^ 2 with hg
  set S : Set ℝ := Ioo a (a + L - ℓ) with hS
  set T : Set ℝ := Ioo (a + ℓ) (a + L) with hT
  have hgc : Continuous g := (continuous_riemannKernelReal.mul hv).pow 2
  have hgcs : HasCompactSupport g := by
    have h : g = phiDoobTest v * phiDoobTest v := by
      funext x
      simp [hg, pow_two]
    rw [h]
    exact (hasCompactSupport_phiDoobTest hvc).mul_left
  have hgint : Integrable g := hgc.integrable_of_hasCompactSupport hgcs
  have hatom : 0 ≤ vonMangoldtAtom n := vonMangoldtAtom_nonneg n
  -- pointwise bound by the indicators of the two strips
  have hpt : ∀ x, phiDoobPrimeCross v n x ≤
      vonMangoldtAtom n * (S.indicator g x + T.indicator g (x + ℓ)) := by
    intro x
    by_cases hx : x ∈ S
    · have hxT : x + ℓ ∈ T := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxT]
      unfold phiDoobPrimeCross
      have h2 : 2 * phiDoobTest v x * phiDoobTest v (x + ℓ) ≤
          phiDoobTest v x ^ 2 + phiDoobTest v (x + ℓ) ^ 2 := two_mul_le_add_sq _ _
      have hcross : 2 * vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + ℓ) *
          v x * v (x + ℓ) = vonMangoldtAtom n * (2 * phiDoobTest v x * phiDoobTest v (x + ℓ)) := by
        unfold phiDoobTest
        ring
      rw [hcross]
      exact mul_le_mul_of_nonneg_left h2 hatom
    · have hzero : phiDoobPrimeCross v n x = 0 := by
        unfold phiDoobPrimeCross
        by_cases hx' : x ∈ Ioo a (a + L)
        · have : v (x + ℓ) = 0 := hsupp _ fun h => hx ⟨hx'.1, by linarith [h.2]⟩
          rw [this]
          ring
        · rw [hsupp x hx']
          ring
      rw [hzero]
      exact mul_nonneg hatom (add_nonneg (Set.indicator_nonneg (fun y _ => sq_nonneg _) _)
        (Set.indicator_nonneg (fun y _ => sq_nonneg _) _))
  have hint1 : Integrable (S.indicator g) := hgint.indicator measurableSet_Ioo
  have hint2 : Integrable (fun x => T.indicator g (x + ℓ)) :=
    (hgint.indicator measurableSet_Ioo).comp_add_right ℓ
  calc ∫ x, phiDoobPrimeCross v n x
      ≤ ∫ x, vonMangoldtAtom n * (S.indicator g x + T.indicator g (x + ℓ)) :=
        integral_mono (integrable_phiDoobPrimeCross hv hvc n)
          ((hint1.add hint2).const_mul _) hpt
    _ = vonMangoldtAtom n * ((∫ x, S.indicator g x) + ∫ x, T.indicator g (x + ℓ)) := by
        rw [integral_const_mul, integral_add hint1 hint2]
    _ = vonMangoldtAtom n * ((∫ x in S, g x) + ∫ x in T, g x) := by
        rw [integral_indicator measurableSet_Ioo,
          integral_add_right_eq_self (fun x => T.indicator g x) ℓ,
          integral_indicator measurableSet_Ioo]

/-! ## The prime-2 domination -/

/-- **Prime-2 domination**: the explicit-weight cross term of the prime `2` is dominated by the
archimedean Lévy form. -/
def PrimeTwoDomination (v : ℝ → ℝ) : Prop :=
  ∫ x, phiDoobPrimeCross v 2 x ≤ weilLevyForm (phiDoobTest v)

/-- On the single-prime-power window, nonnegative Doob energy is exactly prime-2 domination. -/
theorem sourceEnergy_nonneg_iff_primeTwoDomination (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) {a L : ℝ} (hsupp : ∀ x ∉ Ioo a (a + L), v x = 0)
    (hL : L ≤ Real.log 3) :
    0 ≤ sourceEnergy (compactLift v hv hvc) ↔ PrimeTwoDomination v := by
  rw [sourceEnergy_compactLift_eq_levy_sub_cross_two v hv hvc hsupp hL, PrimeTwoDomination,
    sub_nonneg]

/-- **RH forces prime-2 domination** on every primitive test of the single-prime-power window. -/
theorem primeTwoDomination_of_riemannHypothesis (hRH : RiemannHypothesis) {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) {a L : ℝ}
    (hsupp : ∀ x ∉ Ioo a (a + L), v x = 0) (hL : L ≤ Real.log 3)
    (hprim : phiDoobCoshMass v = 0) : PrimeTwoDomination v := by
  rw [← sourceEnergy_nonneg_iff_primeTwoDomination v hv hvc hsupp hL, sourceEnergy_compactLift]
  exact (riemannHypothesis_iff_forall_phiDoobCoshMass_zero_markovEnergy_nonneg.mp hRH) v hv hvc
    hprim

/-- **Prime-free sufficient condition**: boundary coercivity of the Lévy form on the two end strips
of width `L − log 2`, with the explicit weight `log 2 / √2`, gives prime-2 domination. -/
theorem primeTwoDomination_of_strip_coercivity {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) {a L : ℝ} (hsupp : ∀ x ∉ Ioo a (a + L), v x = 0)
    (hcoer : vonMangoldtAtom 2 *
      ((∫ x in Ioo a (a + L - Real.log 2), phiDoobTest v x ^ 2) +
        ∫ x in Ioo (a + Real.log 2) (a + L), phiDoobTest v x ^ 2) ≤
      weilLevyForm (phiDoobTest v)) : PrimeTwoDomination v :=
  (integral_phiDoobPrimeCross_le_strips hv.continuous hvc hsupp 2).trans hcoer

/-- The explicit weight of the prime `2`. -/
theorem vonMangoldtAtom_two : vonMangoldtAtom 2 = Real.log 2 / Real.sqrt 2 := by
  unfold vonMangoldtAtom
  rw [if_pos le_rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

end RHTower.CHMDPolar
