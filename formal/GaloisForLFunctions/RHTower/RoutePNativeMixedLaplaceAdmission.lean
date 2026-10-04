import GaloisForLFunctions.RHTower.RoutePLatePrimeReciprocalFTC
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Admission for the native signed-growth contradiction

The finite early removal mass remains explicit. A proposed exponential
bound on the literal mixed primitive transfers to the corrected primitive
and its continuous reciprocal density. These are intermediate implications
for a contradiction argument; no bound on the actual primitive is assumed
as an axiom or claimed to hold.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower.NativeMixedLaplace

def jumpPrimitive (ε t : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Real.exp (t / 2)⌋₊,
    routePNativeLatePrimeMixedPrimitive ε (2 * Real.log p) * routePLatePrimeReciprocalJump p

private theorem primeClock_mem {p : ℕ} (hp : p.Prime) (t : ℝ) :
    p ∈ Nat.primesLE ⌊Real.exp t⌋₊ ↔ Real.log p ≤ t := by
  rw [Nat.mem_primesLE, and_iff_left hp,
    Nat.le_floor_iff (Real.exp_pos t).le, ← Real.log_le_iff_le_exp]
  exact_mod_cast hp.pos

/-- Exact early/late split of the actual product jumps. -/
theorem jumpPrimitive_split (ε : ℝ) {a t : ℝ} (hat : a ≤ t) :
    jumpPrimitive ε t = jumpPrimitive ε a +
      ∑ p ∈ Nat.primesLE ⌊Real.exp (t / 2)⌋₊,
        if a < 2 * Real.log p then
          routePNativeLatePrimeMixedPrimitive ε (2 * Real.log p) *
            routePLatePrimeReciprocalJump p else 0 := by
  classical
  have hf : (Nat.primesLE ⌊Real.exp (t / 2)⌋₊).filter
      (fun p : ℕ => 2 * Real.log p ≤ a) = Nat.primesLE ⌊Real.exp (a / 2)⌋₊ := by
    ext p
    by_cases hp : p.Prime
    · simp only [Finset.mem_filter, primeClock_mem hp]
      constructor
      · intro h
        linarith [h.2]
      · intro h
        constructor <;> linarith
    · simp [Nat.mem_primesLE, hp]
  unfold jumpPrimitive
  rw [← hf, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : 2 * Real.log (p : ℝ) ≤ a
  · simp [hp, not_lt.mpr hp]
  · simp [hp, lt_of_not_ge hp]

private theorem finite_prime_sum_le_tsum (f : ℕ → ℝ) (N : ℕ)
    (hs : Summable (fun p : Nat.Primes => f p))
    (hn : ∀ p : ℕ, p.Prime → 0 ≤ f p) :
    ∑ p ∈ Nat.primesLE N, f p ≤ ∑' p : Nat.Primes, f p := by
  classical
  change Summable (fun p : {n : ℕ // Nat.Prime n} => f p) at hs
  change ∑ p ∈ Nat.primesLE N, f p ≤ ∑' p : {n : ℕ // Nat.Prime n}, f p
  rw [← Finset.sum_subtype_of_mem f (fun p hp => (Nat.mem_primesLE.mp hp).2)]
  exact hs.sum_le_tsum _ (fun p _ => hn p p.property)

private theorem jumpPrimitive_bound {T a ε b C μ : ℝ}
    (hTa : T ≤ a) (ha : 0 < a) (hb : 0 ≤ b) (hC : 0 ≤ C) (hbμ : b < μ)
    (hQ : ∀ t : ℝ, a < t → |routePNativeLatePrimeMixedPrimitive ε t| ≤ C * Real.exp (b * t))
    (hs : Summable (fun p : Nat.Primes => if T < 2 * Real.log (p : ℕ) then
      Real.exp (-(μ - b) * (2 * Real.log (p : ℕ))) * |routePLatePrimeReciprocalJump p| else 0)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, a < t → |jumpPrimitive ε t| ≤ B * Real.exp (μ * t) := by
  classical
  let f : ℕ → ℝ := fun p => if T < 2 * Real.log p then
    Real.exp (-(μ - b) * (2 * Real.log p)) * |routePLatePrimeReciprocalJump p| else 0
  let S : ℝ := ∑' p : Nat.Primes, f p
  have hf (p : ℕ) : 0 ≤ f p := by dsimp only [f]; split_ifs <;> positivity
  have hS : 0 ≤ S := tsum_nonneg (fun p => hf p)
  refine ⟨|jumpPrimitive ε a| + C * S, by positivity, ?_⟩
  intro t ht
  have hμ : 0 < μ := hb.trans_lt hbμ
  have hμt : 0 ≤ μ * t := mul_nonneg hμ.le (ha.trans ht).le
  have he : 1 ≤ Real.exp (μ * t) := Real.one_le_exp_iff.mpr hμt
  rw [jumpPrimitive_split ε ht.le]
  calc
    _ ≤ |jumpPrimitive ε a| +
        |∑ p ∈ Nat.primesLE ⌊Real.exp (t / 2)⌋₊,
          if a < 2 * Real.log p then routePNativeLatePrimeMixedPrimitive ε (2 * Real.log p) *
            routePLatePrimeReciprocalJump p else 0| := abs_add_le _ _
    _ ≤ |jumpPrimitive ε a| +
        ∑ p ∈ Nat.primesLE ⌊Real.exp (t / 2)⌋₊,
          |if a < 2 * Real.log p then routePNativeLatePrimeMixedPrimitive ε (2 * Real.log p) *
            routePLatePrimeReciprocalJump p else 0| := by
      apply add_le_add le_rfl
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ |jumpPrimitive ε a| +
        ∑ p ∈ Nat.primesLE ⌊Real.exp (t / 2)⌋₊, C * Real.exp (μ * t) * f p := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpa : a < 2 * Real.log (p : ℝ)
      · have hpt : 2 * Real.log (p : ℝ) ≤ t := by
          have hh := (primeClock_mem (Nat.mem_primesLE.mp hp).2 (t / 2)).mp hp
          linarith
        have hew : Real.exp (b * (2 * Real.log p)) ≤
            Real.exp (μ * t) * Real.exp (-(μ - b) * (2 * Real.log p)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left hpt hμ.le]
        rw [if_pos hpa, abs_mul]
        calc
          _ ≤ (C * Real.exp (b * (2 * Real.log p))) *
              |routePLatePrimeReciprocalJump p| :=
            mul_le_mul_of_nonneg_right (hQ _ hpa) (abs_nonneg _)
          _ ≤ (C * (Real.exp (μ * t) * Real.exp (-(μ - b) * (2 * Real.log p)))) *
              |routePLatePrimeReciprocalJump p| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hew hC) (abs_nonneg _)
          _ = _ := by
            dsimp only [f]
            rw [if_pos (hTa.trans_lt hpa)]
            ring
      · rw [if_neg hpa, abs_zero]
        exact mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) (hf p)
    _ = |jumpPrimitive ε a| + C * Real.exp (μ * t) *
        ∑ p ∈ Nat.primesLE ⌊Real.exp (t / 2)⌋₊, f p := by rw [Finset.mul_sum]
    _ ≤ |jumpPrimitive ε a| + C * Real.exp (μ * t) * S := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left
      · exact finite_prime_sum_le_tsum f _ hs (fun p _ => hf p)
      · positivity
    _ ≤ (|jumpPrimitive ε a| + C * S) * Real.exp (μ * t) := by
      nlinarith [mul_le_mul_of_nonneg_left he (abs_nonneg (jumpPrimitive ε a))]

private theorem square_le_exp {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ B * Real.exp (η * t) := by
  let F : ℝ := (2 : ℕ).factorial
  have hF : 0 < F := by dsimp only [F]; exact_mod_cast Nat.factorial_pos 2
  refine ⟨F / η ^ 2, by positivity, ?_⟩
  intro t ht
  have he := Real.pow_div_factorial_le_exp _ (mul_nonneg hη.le ht) 2
  rw [div_le_iff₀ hF, mul_pow] at he
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hη 2)]
  nlinarith only [he]

/-- Under the proposed growth bound, the actual corrected primitive has
every strictly larger exponential envelope. The early jump mass is paid. -/
theorem correctedPrimitive_growth {T a ε b C K μ : ℝ}
    (hTa : T ≤ a) (ha : 0 < a) (hb : 0 ≤ b) (hC : 0 ≤ C) (hK : 0 ≤ K) (hbμ : b < μ)
    (hQ : ∀ t : ℝ, a < t → |routePNativeLatePrimeMixedPrimitive ε t| ≤ C * Real.exp (b * t))
    (hJ : ∀ t : ℝ, a < t → |1 / routePLatePrimeIncrement t| ≤ K * t ^ 2)
    (hs : Summable (fun p : Nat.Primes => if T < 2 * Real.log (p : ℕ) then
      Real.exp (-(μ - b) * (2 * Real.log (p : ℕ))) * |routePLatePrimeReciprocalJump p| else 0)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, a < t →
      |routePNativeMixedCorrectedPrimitive ε t| ≤ B * Real.exp (μ * t) := by
  obtain ⟨Bj, hBj, hj⟩ := jumpPrimitive_bound hTa ha hb hC hbμ hQ hs
  obtain ⟨Bp, hBp, hp⟩ := square_le_exp (sub_pos.mpr hbμ)
  refine ⟨C * K * Bp + Bj, by positivity, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := (ha.trans ht).le
  change |routePNativeLatePrimeMixedPrimitive ε t * (1 / routePLatePrimeIncrement t) -
    jumpPrimitive ε t| ≤ _
  calc
    _ ≤ |routePNativeLatePrimeMixedPrimitive ε t| * |1 / routePLatePrimeIncrement t| +
        |jumpPrimitive ε t| := by
      rw [← abs_mul]
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
        (routePNativeLatePrimeMixedPrimitive ε t * (1 / routePLatePrimeIncrement t)) 0
        (jumpPrimitive ε t)
    _ ≤ (C * Real.exp (b * t)) * (K * (Bp * Real.exp ((μ - b) * t))) +
        Bj * Real.exp (μ * t) := by
      gcongr
      · exact hQ t ht
      · exact (hJ t ht).trans (mul_le_mul_of_nonneg_left (hp t ht0) hK)
      · exact hj t ht
    _ = _ := by
      have he : Real.exp (b * t) * Real.exp ((μ - b) * t) = Real.exp (μ * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = C * K * Bp * (Real.exp (b * t) * Real.exp ((μ - b) * t)) +
            Bj * Real.exp (μ * t) := by ring
        _ = _ := by rw [he]; ring

/-- The continuous density in the native corrected-primitive identity. -/
def density (ε t : ℝ) : ℝ :=
  routePNativeLatePrimeMixedPrimitive ε t *
    (routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2)

private theorem weighted_admission_of_envelope {f : ℝ → ℝ} {a μ lam B : ℝ}
    (hc : ContinuousOn f (Ioi a)) (hμlam : μ < lam)
    (hb : ∀ t : ℝ, a < t → |f t| ≤ B * Real.exp (μ * t)) :
    IntegrableOn (fun t => Real.exp (-lam * t) * f t) (Ioi a) ∧
      Tendsto (fun t => Real.exp (-lam * t) * f t) atTop (𝓝 0) := by
  have hnorm (t : ℝ) (ht : a < t) :
      ‖Real.exp (-lam * t) * f t‖ ≤ B * Real.exp ((μ - lam) * t) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-lam * t) * (B * Real.exp (μ * t)) :=
        mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos _).le
      _ = B * (Real.exp (-lam * t) * Real.exp (μ * t)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  constructor
  · apply ((integrableOn_exp_mul_Ioi (sub_neg.mpr hμlam) a).const_mul B).mono'
    · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        hc).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hnorm t ht
  · have he : Tendsto (fun t : ℝ => Real.exp ((μ - lam) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        ((tendsto_const_mul_atBot_of_neg (sub_neg.mpr hμlam)).mpr tendsto_id)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun t : ℝ => B * Real.exp ((μ - lam) * t)) atTop (𝓝 0) by
        simpa only [mul_zero] using he.const_mul B)
    · exact Eventually.of_forall (fun _ => norm_nonneg _)
    · filter_upwards [eventually_gt_atTop a] with t ht
      exact hnorm t ht

private theorem density_admission {T a ε b C lam : ℝ}
    (hTa : T ≤ a) (ha : 0 < a)
    (hQ : ∀ t : ℝ, a < t → |routePNativeLatePrimeMixedPrimitive ε t| ≤ C * Real.exp (b * t))
    (hi : IntegrableOn (fun t => Real.exp (-(lam - b) * t) * routePLatePrimeVelocity t /
      routePLatePrimeIncrement t ^ 2) (Ioi T)) :
    IntegrableOn (fun t => Real.exp (-lam * t) * density ε t) (Ioi a) := by
  have hQcont : ContinuousOn (routePNativeLatePrimeMixedPrimitive ε) (Ioi a) := by
    intro t ht
    exact (continuousAt_routePNativeLatePrimeMixedPrimitive ε (ha.trans ht)).continuousWithinAt
  have hmQ := hQcont.aestronglyMeasurable (μ := volume) measurableSet_Ioi
  have hmR : Measurable (fun t => routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2) :=
    measurable_routePLatePrimeVelocity.div (measurable_routePLatePrimeIncrement.pow_const 2)
  have hmE : Measurable (fun t : ℝ => Real.exp (-lam * t)) := by fun_prop
  apply (((hi.mono_set (Ioi_subset_Ioi hTa)).norm).const_mul C).mono'
  · exact hmE.aestronglyMeasurable.restrict.mul (hmQ.mul hmR.aestronglyMeasurable.restrict)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he : Real.exp (-lam * t) * Real.exp (b * t) = Real.exp (-(lam - b) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = Real.exp (-lam * t) * |routePNativeLatePrimeMixedPrimitive ε t| *
          |routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2| := by
        rw [Real.norm_eq_abs, density, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
        ring
      _ ≤ Real.exp (-lam * t) * (C * Real.exp (b * t)) *
          |routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hQ t ht) (Real.exp_pos _).le) (abs_nonneg _)
      _ = C * (Real.exp (-(lam - b) * t) *
          |routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2|) := by
        calc
          _ = C * ((Real.exp (-lam * t) * Real.exp (b * t)) *
              |routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2|) := by ring
          _ = _ := by rw [he]
      _ = C * ‖Real.exp (-(lam - b) * t) * routePLatePrimeVelocity t /
          routePLatePrimeIncrement t ^ 2‖ := by
        simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _)]
        ring

/-- One native late ray supplies both ordinary Laplace admissions and the
vanishing terminal term under the proposed growth bound. The bound is the
contradiction hypothesis to be discharged by the source's Hardy barrier. -/
theorem exists_growthTransfer :
    ∃ T : ℝ, 0 < T ∧ ∀ ε b a C : ℝ, T ≤ a → 0 ≤ b → 0 ≤ C →
      (∀ t : ℝ, a < t → |routePNativeLatePrimeMixedPrimitive ε t| ≤ C * Real.exp (b * t)) →
      ∀ lam : ℝ, b < lam →
        IntegrableOn (fun t => Real.exp (-lam * t) * routePNativeMixedCorrectedPrimitive ε t) (Ioi a) ∧
        IntegrableOn (fun t => Real.exp (-lam * t) * density ε t) (Ioi a) ∧
        Tendsto (fun t => Real.exp (-lam * t) * routePNativeMixedCorrectedPrimitive ε t) atTop (𝓝 0) := by
  obtain ⟨Tb, K, hTb, hK, hJ, _⟩ := exists_routePLatePrimeReciprocalBounds
  obtain ⟨Ti, _, hi⟩ := exists_routePLatePrimeReciprocalAdmission
  obtain ⟨Tc, _, hc⟩ := exists_routePNativeMixedCorrectedPrimitiveCalculus
  refine ⟨max Tb (max Ti Tc), hTb.trans_le (le_max_left _ _), ?_⟩
  intro ε b a C hTa hb hC hQ lam hblam
  have hba : Tb ≤ a := (le_max_left _ _).trans hTa
  have hia : Ti ≤ a := ((le_max_left _ _).trans (le_max_right _ _)).trans hTa
  have hca : Tc ≤ a := ((le_max_right _ _).trans (le_max_right _ _)).trans hTa
  have ha : 0 < a := hTb.trans_le hba
  let μ : ℝ := (b + lam) / 2
  have hbμ : b < μ := by dsimp only [μ]; linarith
  have hμlam : μ < lam := by dsimp only [μ]; linarith
  obtain ⟨B, _, hP⟩ := correctedPrimitive_growth hia ha hb hC hK.le hbμ hQ
    (fun t ht => (hJ t (hba.trans_lt ht)).2) (hi (μ - b) (sub_pos.mpr hbμ)).2
  have hp := weighted_admission_of_envelope
    ((hc ε).1.mono (Ioi_subset_Ioi hca)) hμlam hP
  exact ⟨hp.1, density_admission hia ha hQ (hi (lam - b) (sub_pos.mpr hblam)).1, hp.2⟩

end RHTower.NativeMixedLaplace
