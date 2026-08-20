import GaloisForLFunctions.RHTower.PrimeHigherMertens
import Mathlib

/-!
# The endpoint remainder estimate for the prime boundary layer

For a test function `r` on `(0,1]` vanishing to order `M+1` at the collapsed endpoint, the
prime-harmonic boundary defect

`D_x(r) = ∑_{p ≤ x} r(log p / log x)/p - ∫_0^1 r(u) du/u`

is `O(L^{-M-1})` with `L = log x`, uniformly in `r` given the two bounds `|r(u)| ≤ A u^{M+1}` and
`|r'(u)| ≤ A u^M`.

The proof is Abel summation of the prime-log weight against `θ` with the Abel weight
`f_r(t) = r(log t / L)/(t log t)`.  Integration by parts converts the elementary part into
`∫_{log 2/L}^1 r(u) du/u`, which is the target integral up to the endpoint sliver
`∫_0^{log 2/L}`, and the remaining `θ`-error integral is dominated by
`(A/L^{M+1}) · jetTailWeight M`, an integrable envelope built from the logarithmic
de la Vallée Poussin weights of `PrimeHigherMertens`.

Together with the monomial expansions of `PrimeHigherMertens` this is the analytic core of the
endpoint-jet theorem: every algebraic order of the prime boundary layer is a distributional jet at
the collapsed endpoint.
-/

set_option maxHeartbeats 1600000

open Filter Topology Set MeasureTheory Asymptotics

namespace RHTower

noncomputable section

/-! ## The Abel weight of a boundary test function -/

/-- `f_r(t) = r(log t / L)/(t log t)`, the Abel weight whose Chebyshev sum is
`∑_{p ≤ x} r(log p / L)/p`. -/
def jetWeight (r : ℝ → ℝ) (L t : ℝ) : ℝ := r (Real.log t / L) / (t * Real.log t)

/-- The derivative of the Abel weight. -/
def derivJetWeight (r r' : ℝ → ℝ) (L t : ℝ) : ℝ :=
  r' (Real.log t / L) / (L * t ^ 2 * Real.log t)
    - r (Real.log t / L) * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)

theorem hasDerivAt_jetWeight {r r' : ℝ → ℝ} {L t : ℝ} (hL : 0 < L) (ht : 1 < t)
    (hr : HasDerivAt r (r' (Real.log t / L)) (Real.log t / L)) :
    HasDerivAt (jetWeight r L) (derivJetWeight r r' L t) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have hu : HasDerivAt (fun s : ℝ => Real.log s / L) (t⁻¹ / L) t :=
    (Real.hasDerivAt_log ht0.ne').div_const L
  have hnum : HasDerivAt (fun s : ℝ => r (Real.log s / L))
      (r' (Real.log t / L) * (t⁻¹ / L)) t := hr.comp t hu
  have hden : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t := by
    have h := (hasDerivAt_id t).mul (Real.hasDerivAt_log ht0.ne')
    rw [Pi.mul_def] at h
    simp only [id_eq] at h
    refine h.congr_deriv ?_
    field_simp
  have hne : t * Real.log t ≠ 0 := by positivity
  have hdiv := hnum.div hden hne
  refine hdiv.congr_deriv ?_
  rw [derivJetWeight]
  field_simp

theorem jetWeight_mul_primeLogWeight (r : ℝ → ℝ) (L : ℝ) (n : ℕ) :
    jetWeight r L n * primeLogWeight n
      = if n.Prime then r (Real.log n / L) / n else 0 := by
  rw [jetWeight, primeLogWeight]
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    field_simp
  · rw [if_neg hp, if_neg hp, mul_zero]

/-! ## Continuity of the Abel weight and its derivative -/


theorem mapsTo_logDiv {L x : ℝ} (hL : 0 < L) (_hx : 2 ≤ x) (hLx : Real.log x = L) :
    MapsTo (fun t : ℝ => Real.log t / L) (Icc 2 x) (Ioc (0 : ℝ) 1) := by
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := ht.1
  have htx : t ≤ x := ht.2
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  constructor
  · positivity
  · rw [div_le_one hL, ← hLx]
    exact Real.log_le_log (by linarith) htx

theorem continuousOn_logDiv {L x : ℝ} :
    ContinuousOn (fun t : ℝ => Real.log t / L) (Icc 2 x) := by
  intro t ht
  have ht0 : t ≠ 0 := by
    have := ht.1
    intro h
    rw [h] at this
    linarith
  exact ((Real.continuousAt_log ht0).div_const L).continuousWithinAt

theorem continuousOn_mulLog {x : ℝ} : ContinuousOn (fun t : ℝ => t * Real.log t) (Icc 2 x) := by
  intro t ht
  have ht0 : t ≠ 0 := by
    have := ht.1
    intro h
    rw [h] at this
    linarith
  exact (continuousAt_id.mul (Real.continuousAt_log ht0)).continuousWithinAt

theorem continuousOn_jetWeight {r r' : ℝ → ℝ} {L x : ℝ} (hL : 0 < L) (hx : 2 ≤ x)
    (hLx : Real.log x = L) (hr : ∀ u ∈ Ioc (0 : ℝ) 1, HasDerivAt r (r' u) u) :
    ContinuousOn (jetWeight r L) (Icc 2 x) := by
  have hrc : ContinuousOn r (Ioc (0 : ℝ) 1) :=
    fun u hu => (hr u hu).continuousAt.continuousWithinAt
  refine ContinuousOn.div
    (hrc.comp (continuousOn_logDiv) (mapsTo_logDiv hL hx hLx)) continuousOn_mulLog ?_
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := ht.1
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  positivity

theorem continuousOn_derivJetWeight {r r' : ℝ → ℝ} {L x : ℝ} (hL : 0 < L) (hx : 2 ≤ x)
    (hLx : Real.log x = L) (hr : ∀ u ∈ Ioc (0 : ℝ) 1, HasDerivAt r (r' u) u)
    (hr' : ContinuousOn r' (Ioc (0 : ℝ) 1)) :
    ContinuousOn (derivJetWeight r r' L) (Icc 2 x) := by
  have hrc : ContinuousOn r (Ioc (0 : ℝ) 1) :=
    fun u hu => (hr u hu).continuousAt.continuousWithinAt
  have hmaps := mapsTo_logDiv hL hx hLx
  have hlogdiv := continuousOn_logDiv (L := L) (x := x)
  have hne1 : ∀ t ∈ Icc (2 : ℝ) x, L * t ^ 2 * Real.log t ≠ 0 := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    positivity
  have hne2 : ∀ t ∈ Icc (2 : ℝ) x, t ^ 2 * Real.log t ^ 2 ≠ 0 := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    positivity
  have hlogcont : ContinuousOn Real.log (Icc 2 x) := by
    intro t ht
    have ht0 : t ≠ 0 := by
      have := ht.1
      intro h
      rw [h] at this
      linarith
    exact (Real.continuousAt_log ht0).continuousWithinAt
  refine ContinuousOn.sub ?_ ?_
  · exact ContinuousOn.div (hr'.comp hlogdiv hmaps)
      ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hlogcont) hne1
  · exact ContinuousOn.div ((hrc.comp hlogdiv hmaps).mul (hlogcont.add continuousOn_const))
      ((continuousOn_id.pow 2).mul (hlogcont.pow 2)) hne2

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory


theorem primeBoundaryJetSumIoc_eq {r r' : ℝ → ℝ} {L x : ℝ} (hL : 0 < L) (hx : 2 ≤ x)
    (hr : ∀ t : ℝ, 2 ≤ t → t ≤ x → HasDerivAt r (r' (Real.log t / L)) (Real.log t / L))
    (hcont : ContinuousOn (derivJetWeight r r' L) (Icc 2 x)) :
    (∑ n ∈ Finset.Ioc 2 ⌊x⌋₊, (if n.Prime then r (Real.log n / L) / n else 0))
      = jetWeight r L x * Chebyshev.theta x - jetWeight r L 2 * Chebyshev.theta 2
        - ∫ t in Ioc (2 : ℝ) x, derivJetWeight r r' L t * Chebyshev.theta t := by
  have hderiv : ∀ t ∈ Icc (2 : ℝ) x, HasDerivAt (jetWeight r L) (derivJetWeight r r' L t) t := by
    intro t ht
    exact hasDerivAt_jetWeight hL (by have := ht.1; linarith) (hr t ht.1 ht.2)
  have hint : IntegrableOn (deriv (jetWeight r L)) (Icc 2 x) := by
    refine hcont.integrableOn_Icc.congr_fun (fun t ht => ?_) measurableSet_Icc
    exact ((hderiv t ht).deriv).symm
  have habel := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ) primeLogWeight
    (f := jetWeight r L) (a := (2 : ℝ)) (b := x) (by norm_num) hx
    (fun t ht => (hderiv t ht).differentiableAt) hint
  simp only [sum_primeLogWeight_eq_theta] at habel
  rw [show (⌊(2 : ℝ)⌋₊) = 2 from by norm_num] at habel
  have hint2 : (∫ t in Ioc (2 : ℝ) x, deriv (jetWeight r L) t * Chebyshev.theta t)
      = ∫ t in Ioc (2 : ℝ) x, derivJetWeight r r' L t * Chebyshev.theta t := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [(hderiv t ⟨le_of_lt ht.1, ht.2⟩).deriv]
  rw [← hint2, ← habel]
  exact Finset.sum_congr rfl fun n _ => (jetWeight_mul_primeLogWeight r L n).symm

/-! ## The main term: substitution and integration by parts -/

theorem integral_jetWeight_eq {r r' : ℝ → ℝ} {L x : ℝ} (hL : 0 < L) (hx : 2 ≤ x)
    (hLx : Real.log x = L) (hr : ∀ u ∈ Ioc (0 : ℝ) 1, HasDerivAt r (r' u) u) :
    (∫ t in (2 : ℝ)..x, jetWeight r L t) = ∫ u in (Real.log 2 / L)..(1 : ℝ), r u / u := by
  have huIcc : uIcc (2 : ℝ) x = Icc 2 x := uIcc_of_le hx
  have hderiv : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt (fun s : ℝ => Real.log s / L) (t⁻¹ / L) t := by
    intro t ht
    rw [huIcc] at ht
    have ht0 : (0 : ℝ) < t := by have := ht.1; linarith
    exact (Real.hasDerivAt_log ht0.ne').div_const L
  have hcont' : ContinuousOn (fun t : ℝ => t⁻¹ / L) (uIcc (2 : ℝ) x) := by
    rw [huIcc]
    intro t ht
    have ht0 : t ≠ 0 := by
      have := ht.1
      intro h
      rw [h] at this
      linarith
    exact ((continuousAt_id.inv₀ ht0).div_const L).continuousWithinAt
  have hmaps : MapsTo (fun t : ℝ => Real.log t / L) (uIcc (2 : ℝ) x) (Ioc (0 : ℝ) 1) := by
    rw [huIcc]
    exact mapsTo_logDiv hL hx hLx
  have hrc : ContinuousOn r (Ioc (0 : ℝ) 1) :=
    fun u hu => (hr u hu).continuousAt.continuousWithinAt
  have hg : ContinuousOn (fun u : ℝ => r u / u)
      ((fun t : ℝ => Real.log t / L) '' uIcc (2 : ℝ) x) := by
    refine (hrc.div continuousOn_id ?_).mono ?_
    · intro u hu
      exact ne_of_gt hu.1
    · exact image_subset_iff.mpr hmaps
  have h := intervalIntegral.integral_deriv_smul_comp' hderiv hcont' hg
  have hfa : Real.log (2 : ℝ) / L = Real.log 2 / L := rfl
  have hfb : Real.log x / L = 1 := by rw [hLx, div_self hL.ne']
  rw [hfb] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [huIcc] at ht
  have ht2 : (2 : ℝ) ≤ t := ht.1
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  rw [jetWeight, Function.comp_apply, smul_eq_mul]
  field_simp

theorem integral_derivJetWeight_mul_id_eq {r r' : ℝ → ℝ} {L x : ℝ} (hL : 0 < L) (hx : 2 ≤ x)
    (hLx : Real.log x = L) (hr : ∀ u ∈ Ioc (0 : ℝ) 1, HasDerivAt r (r' u) u)
    (hr' : ContinuousOn r' (Ioc (0 : ℝ) 1)) :
    (∫ t in (2 : ℝ)..x, derivJetWeight r r' L t * t)
      = jetWeight r L x * x - jetWeight r L 2 * 2 - ∫ t in (2 : ℝ)..x, jetWeight r L t := by
  have huIcc : uIcc (2 : ℝ) x = Icc 2 x := uIcc_of_le hx
  have hmaps := mapsTo_logDiv hL hx hLx
  have hprod : ∀ t ∈ uIcc (2 : ℝ) x,
      HasDerivAt (fun s : ℝ => jetWeight r L s * s)
        (derivJetWeight r r' L t * t + jetWeight r L t) t := by
    intro t ht
    rw [huIcc] at ht
    have ht1 : (1 : ℝ) < t := by have := ht.1; linarith
    have hderiv := hasDerivAt_jetWeight hL ht1 (hr _ (hmaps ht))
    have h := hderiv.mul (hasDerivAt_id t)
    rw [Pi.mul_def] at h
    simp only [id_eq] at h
    refine h.congr_deriv ?_
    ring
  have hcontD : ContinuousOn (fun t : ℝ => derivJetWeight r r' L t * t + jetWeight r L t)
      (Icc 2 x) :=
    ((continuousOn_derivJetWeight hL hx hLx hr hr').mul continuousOn_id).add
      (continuousOn_jetWeight hL hx hLx hr)
  have hI : IntervalIntegrable (fun t : ℝ => derivJetWeight r r' L t * t + jetWeight r L t)
      volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact hcontD.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hI1 : IntervalIntegrable (fun t : ℝ => derivJetWeight r r' L t * t) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact (((continuousOn_derivJetWeight hL hx hLx hr hr').mul
      continuousOn_id).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hI2 : IntervalIntegrable (jetWeight r L) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact ((continuousOn_jetWeight hL hx hLx hr).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod hI
  rw [intervalIntegral.integral_add hI1 hI2] at hftc
  linarith [hftc]

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory

/-! ## The exact endpoint decomposition -/

/-- `D_x(r) = ∑_{p ≤ x} r(log p / log x)/p - ∫_0^1 r(u) du/u`, the prime-harmonic boundary
defect of the card. -/
def primeBoundaryDefect (r : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if n.Prime then r (Real.log n / Real.log x) / n else 0))
    - ∫ u in (0 : ℝ)..1, r u / u

theorem primeBoundaryJetSum_split (r : ℝ → ℝ) (L : ℝ) {x : ℝ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if n.Prime then r (Real.log n / L) / n else 0))
      = (∑ n ∈ Finset.Ioc 2 ⌊x⌋₊, (if n.Prime then r (Real.log n / L) / n else 0))
        + r (Real.log 2 / L) / 2 := by
  have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hunion : Finset.Icc 0 2 ∪ Finset.Ioc 2 ⌊x⌋₊ = Finset.Icc 0 ⌊x⌋₊ := by
    ext a
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 0 2) (Finset.Ioc 2 ⌊x⌋₊) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    have h1 : a ≤ 2 := (Finset.mem_Icc.mp ha).2
    have h2 : 2 < a := (Finset.mem_Ioc.mp ha').1
    omega
  rw [← hunion, Finset.sum_union hdisj, add_comm]
  congr 1
  rw [show Finset.Icc 0 2 = {0, 1, 2} from by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    if_neg (by decide : ¬ Nat.Prime 0), if_neg (by decide : ¬ Nat.Prime 1),
    if_pos (by decide : Nat.Prime 2)]
  norm_num

theorem primeBoundaryDefect_eq {r r' : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x)
    (hr : ∀ u ∈ Ioc (0 : ℝ) 1, HasDerivAt r (r' u) u)
    (hr' : ContinuousOn r' (Ioc (0 : ℝ) 1))
    (hint : IntervalIntegrable (fun u : ℝ => r u / u) volume 0 1) :
    primeBoundaryDefect r x
      = jetWeight r (Real.log x) x * (Chebyshev.theta x - x)
        + jetWeight r (Real.log x) 2 * (2 - Chebyshev.theta 2)
        + r (Real.log 2 / Real.log x) / 2
        - (∫ u in (0 : ℝ)..(Real.log 2 / Real.log x), r u / u)
        - ∫ t in Ioc (2 : ℝ) x, derivJetWeight r r' (Real.log x) t * t * thetaError t := by
  set L := Real.log x with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hLx : Real.log x = L := rfl
  have hmaps := mapsTo_logDiv hL hx hLx
  have habel := primeBoundaryJetSumIoc_eq (r := r) (r' := r') hL hx
    (fun t ht ht' => hr _ (hmaps ⟨ht, ht'⟩)) (continuousOn_derivJetWeight hL hx hLx hr hr')
  have hsplitTheta : (∫ t in Ioc (2 : ℝ) x, derivJetWeight r r' L t * Chebyshev.theta t)
      = (∫ t in (2 : ℝ)..x, derivJetWeight r r' L t * t)
        + ∫ t in Ioc (2 : ℝ) x, derivJetWeight r r' L t * t * thetaError t := by
    have hpt : ∀ t ∈ Ioc (2 : ℝ) x, derivJetWeight r r' L t * Chebyshev.theta t
        = derivJetWeight r r' L t * t + derivJetWeight r r' L t * t * thetaError t := by
      intro t ht
      have ht0 : (0 : ℝ) < t := by have := ht.1; linarith
      rw [theta_eq_mul_thetaError ht0]
      ring
    have hI1 : IntegrableOn (fun t : ℝ => derivJetWeight r r' L t * t) (Ioc (2 : ℝ) x) :=
      (((continuousOn_derivJetWeight hL hx hLx hr hr').mul
        continuousOn_id).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hI2 : IntegrableOn (fun t : ℝ => derivJetWeight r r' L t * t * thetaError t)
        (Ioc (2 : ℝ) x) := by
      have hcont : ContinuousOn (fun t : ℝ => derivJetWeight r r' L t * t) (Icc 2 x) :=
        (continuousOn_derivJetWeight hL hx hLx hr hr').mul continuousOn_id
      have h := ((integrableOn_thetaError x).mul_continuousOn hcont isCompact_Icc)
      refine (h.congr_fun (fun t _ => by ring) measurableSet_Icc).mono_set Ioc_subset_Icc_self
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add hI1 hI2,
      intervalIntegral.integral_of_le hx]
  have hbyparts := integral_derivJetWeight_mul_id_eq hL hx hLx hr hr'
  have hsubst := integral_jetWeight_eq hL hx hLx hr
  have hsplitInt : (∫ u in (0 : ℝ)..1, r u / u)
      = (∫ u in (0 : ℝ)..(Real.log 2 / L), r u / u) + ∫ u in (Real.log 2 / L)..1, r u / u := by
    have h1 : IntervalIntegrable (fun u : ℝ => r u / u) volume 0 (Real.log 2 / L) := by
      refine hint.mono_set ?_
      rw [uIcc_of_le (by positivity), uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Icc_subset_Icc le_rfl (by
        rw [div_le_one hL, ← hLx]
        exact Real.log_le_log (by norm_num) (by linarith))
    have h2 : IntervalIntegrable (fun u : ℝ => r u / u) volume (Real.log 2 / L) 1 := by
      refine hint.mono_set ?_
      rw [uIcc_of_le (by
        rw [div_le_one hL, ← hLx]
        exact Real.log_le_log (by norm_num) (by linarith)),
        uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Icc_subset_Icc (by positivity) le_rfl
    exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  rw [primeBoundaryDefect, primeBoundaryJetSum_split r L hx, habel, hsplitTheta, hbyparts,
    hsubst, hsplitInt]
  ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory

/-! ## The master endpoint estimate -/

/-- The integrable envelope controlling the `θ`-error part of the endpoint defect. -/
def jetTailWeight (M : ℕ) (t : ℝ) : ℝ :=
  ((1 / Real.log 2) * (Real.log t) ^ M
      + ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1))
    * |thetaError t| / t

theorem jetTailWeight_nonneg (M : ℕ) {t : ℝ} (ht : 2 < t) : 0 ≤ jetTailWeight M t := by
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [jetTailWeight]
  have h1 : (0 : ℝ) ≤ (1 / Real.log 2) * (Real.log t) ^ M := by positivity
  have h2 : (0 : ℝ) ≤ ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1) := by
    positivity
  exact div_nonneg (mul_nonneg (by linarith) (abs_nonneg _)) ht0.le

theorem integrableOn_jetTailWeight (M : ℕ) : IntegrableOn (jetTailWeight M) (Ioi (2 : ℝ)) := by
  obtain ⟨c, hc0, hO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hC.and (Filter.eventually_ge_atTop (2 : ℝ)))
  have hT2 : (2 : ℝ) ≤ T := (hT T le_rfl).2
  have hsplit : Ioc (2 : ℝ) T ∪ Ioi T = Ioi (2 : ℝ) := Ioc_union_Ioi_eq_Ioi hT2
  have hmeas : Measurable (jetTailWeight M) := by
    refine Measurable.div ?_ measurable_id
    refine Measurable.mul ?_ measurable_thetaError.abs
    exact ((Real.measurable_log.pow_const M).const_mul _).add
      ((Real.measurable_log.pow_const (M + 1)).const_mul _)
  rw [← hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hcont : ContinuousOn
        (fun t : ℝ => ((1 / Real.log 2) * (Real.log t) ^ M
          + ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1)) / t) (Icc 2 T) := by
      intro t ht
      have ht0 : t ≠ 0 := by
        have := ht.1
        intro h
        rw [h] at this
        linarith
      have hlogc : ContinuousAt Real.log t := Real.continuousAt_log ht0
      exact ((((hlogc.pow M).const_mul _).add ((hlogc.pow (M + 1)).const_mul _)).div
        continuousAt_id ht0).continuousWithinAt
    have h0 := ((integrableOn_thetaError T).mul_continuousOn hcont isCompact_Icc)
    have h : IntegrableOn (fun t : ℝ => |thetaError t *
        (((1 / Real.log 2) * (Real.log t) ^ M
          + ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1)) / t)|)
        (Icc 2 T) := h0.abs
    refine (IntegrableOn.congr_fun h (fun t ht => ?_)
      measurableSet_Icc).mono_set Ioc_subset_Icc_self
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have htpos : (0 : ℝ) < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hgnn : (0 : ℝ) ≤ ((1 / Real.log 2) * (Real.log t) ^ M
        + ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1)) / t := by
      have h1 : (0 : ℝ) ≤ (1 / Real.log 2) * (Real.log t) ^ M := by positivity
      have h2 : (0 : ℝ) ≤ ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1) := by
        positivity
      exact div_nonneg (by linarith) htpos.le
    rw [abs_mul, abs_of_nonneg hgnn, jetTailWeight]
    ring
  · set g : ℝ → ℝ := fun t : ℝ =>
      |C| * ((1 / Real.log 2) *
          ((Real.log t) ^ M * Real.exp (-c * Real.sqrt (Real.log t)) / t))
        + |C| * (((1 / Real.log 2) + (1 / Real.log 2) ^ 2) *
          ((Real.log t) ^ (M + 1) * Real.exp (-c * Real.sqrt (Real.log t)) / t)) with hg
    have hgint : IntegrableOn g (Ioi (2 : ℝ)) := by
      refine Integrable.add ?_ ?_
      · exact ((integrableOn_logPow_pntErrorWeight hc0 M).const_mul _).const_mul |C|
      · exact ((integrableOn_logPow_pntErrorWeight hc0 (M + 1)).const_mul _).const_mul |C|
    refine Integrable.mono (hgint.mono_set (Ioi_subset_Ioi hT2))
      (hmeas.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htT : T ≤ t := le_of_lt ht
    have ht2 : (2 : ℝ) < t := lt_of_le_of_lt hT2 ht
    have htpos : (0 : ℝ) < t := by linarith
    have hlog : 0 < Real.log t := Real.log_pos (by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbound := (hT t htT).1
    have herr : |thetaError t| ≤ |C| * Real.exp (-c * Real.sqrt (Real.log t)) := by
      have h1 : ‖(Chebyshev.theta - id : ℝ → ℝ) t‖
          ≤ C * ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖ := hbound
      have h2 : ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖
          = t * Real.exp (-c * Real.sqrt (Real.log t)) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h3 : ‖(Chebyshev.theta - id : ℝ → ℝ) t‖ = |Chebyshev.theta t - t| := by
        simp [Real.norm_eq_abs]
      rw [h2, h3] at h1
      have hnum : |Chebyshev.theta t - t|
          ≤ |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) :=
        h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      have hdiv : thetaError t = (Chebyshev.theta t - t) / t := by
        rw [thetaError]
        field_simp
      rw [hdiv, abs_div, abs_of_pos htpos, div_le_iff₀ htpos]
      calc |Chebyshev.theta t - t|
          ≤ |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) := hnum
        _ = |C| * Real.exp (-c * Real.sqrt (Real.log t)) * t := by ring
    have hcoef : (0 : ℝ) ≤ (1 / Real.log 2) * (Real.log t) ^ M
        + ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1) := by
      have h1 : (0 : ℝ) ≤ (1 / Real.log 2) * (Real.log t) ^ M := by positivity
      have h2 : (0 : ℝ) ≤ ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1) := by
        positivity
      linarith
    have hgnn : 0 ≤ g t := by
      have he : (0 : ℝ) < Real.exp (-c * Real.sqrt (Real.log t)) := Real.exp_pos _
      have h1 : (0 : ℝ) ≤ (Real.log t) ^ M * Real.exp (-c * Real.sqrt (Real.log t)) / t :=
        div_nonneg (mul_nonneg (pow_nonneg hlog.le _) he.le) htpos.le
      have h2 : (0 : ℝ) ≤ (Real.log t) ^ (M + 1) * Real.exp (-c * Real.sqrt (Real.log t)) / t :=
        div_nonneg (mul_nonneg (pow_nonneg hlog.le _) he.le) htpos.le
      rw [hg]
      have hc1 : (0 : ℝ) ≤ 1 / Real.log 2 := by positivity
      have hc2 : (0 : ℝ) ≤ (1 / Real.log 2) + (1 / Real.log 2) ^ 2 := by positivity
      exact add_nonneg (mul_nonneg (abs_nonneg C) (mul_nonneg hc1 h1))
        (mul_nonneg (abs_nonneg C) (mul_nonneg hc2 h2))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgnn, jetTailWeight, abs_div,
      abs_of_pos htpos, abs_mul, abs_of_nonneg hcoef, abs_abs]
    rw [div_le_iff₀ htpos]
    have hstep : ((1 / Real.log 2) * (Real.log t) ^ M
        + ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1)) * |thetaError t|
        ≤ ((1 / Real.log 2) * (Real.log t) ^ M
          + ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1))
          * (|C| * Real.exp (-c * Real.sqrt (Real.log t))) :=
      mul_le_mul_of_nonneg_left herr hcoef
    refine hstep.trans_eq ?_
    rw [hg]
    field_simp

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory

theorem intervalIntegrable_rDiv {M : ℕ} {r r' : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hr : ∀ u ∈ Ioc (0 : ℝ) 1, HasDerivAt r (r' u) u)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, |r u| ≤ A * u ^ (M + 1)) :
    IntervalIntegrable (fun u : ℝ => r u / u) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hmeas : AEStronglyMeasurable (fun u : ℝ => r u / u) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    intro u hu
    exact ((hr u hu).continuousAt.continuousWithinAt).div continuousWithinAt_id (ne_of_gt hu.1)
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => A) (integrable_const A) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hupos : (0 : ℝ) < u := hu.1
  have hule : u ≤ 1 := hu.2
  have h1 : |r u| ≤ A * u ^ (M + 1) := hb u hu
  have hpow : u ^ (M + 1) ≤ u := by
    calc u ^ (M + 1) = u ^ M * u := by ring
      _ ≤ 1 * u := by
          refine mul_le_mul_of_nonneg_right (pow_le_one₀ hupos.le hule) hupos.le
      _ = u := one_mul u
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hupos, div_le_iff₀ hupos]
  calc |r u| ≤ A * u ^ (M + 1) := h1
    _ ≤ A * u := mul_le_mul_of_nonneg_left hpow hA

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory

/-- **The endpoint remainder estimate.**  A test function vanishing to order `M+1` at the
collapsed endpoint contributes only `O(L^{-M-1})` to the prime-harmonic boundary defect. -/
theorem exists_abs_primeBoundaryDefect_le (M : ℕ) :
    ∃ B X₀ : ℝ, 0 ≤ B ∧ 4 ≤ X₀ ∧
      ∀ (r r' : ℝ → ℝ) (A : ℝ), 0 ≤ A →
        (∀ u ∈ Ioc (0 : ℝ) 1, HasDerivAt r (r' u) u) →
        ContinuousOn r' (Ioc (0 : ℝ) 1) →
        (∀ u ∈ Ioc (0 : ℝ) 1, |r u| ≤ A * u ^ (M + 1)) →
        (∀ u ∈ Ioc (0 : ℝ) 1, |r' u| ≤ A * u ^ M) →
        ∀ x : ℝ, X₀ ≤ x → |primeBoundaryDefect r x| ≤ A * B / (Real.log x) ^ (M + 1) := by
  obtain ⟨c, hc0, hO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hC.and (Filter.eventually_ge_atTop (4 : ℝ)))
  have hT4 : (4 : ℝ) ≤ T := (hT T le_rfl).2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := (((2 * (M + 1)).factorial : ℕ) : ℝ) / c ^ (2 * (M + 1)) with hK
  have hKnn : 0 ≤ K := by
    have : (0 : ℝ) < (((2 * (M + 1)).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity
  set B₅ : ℝ := ∫ t in Ioi (2 : ℝ), jetTailWeight M t with hB5
  have hB5nn : 0 ≤ B₅ := by
    rw [hB5]
    exact setIntegral_nonneg measurableSet_Ioi fun t ht => jetTailWeight_nonneg M ht
  refine ⟨|C| * K + (Real.log 2) ^ (M + 1) * |2 - Chebyshev.theta 2| / (2 * Real.log 2)
      + (Real.log 2) ^ (M + 1) / 2 + (Real.log 2) ^ (M + 1) / ((M : ℝ) + 1) + B₅, T,
    by
      have h1 : (0 : ℝ) ≤ |C| * K := by positivity
      have h2 : (0 : ℝ) ≤ (Real.log 2) ^ (M + 1) * |2 - Chebyshev.theta 2| / (2 * Real.log 2) := by
        positivity
      have h3 : (0 : ℝ) ≤ (Real.log 2) ^ (M + 1) / 2 := by positivity
      have h4 : (0 : ℝ) ≤ (Real.log 2) ^ (M + 1) / ((M : ℝ) + 1) := by positivity
      linarith, hT4, ?_⟩
  intro r r' A hA hr hr' hb hb' x hxT
  have hx4 : (4 : ℝ) ≤ x := le_trans hT4 hxT
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  set L := Real.log x with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hL1 : 1 ≤ L := by
    have he : Real.exp 1 ≤ x := by nlinarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) he
  have hLpow : (0 : ℝ) < L ^ (M + 1) := by positivity
  have hLx : Real.log x = L := rfl
  -- the endpoint parameter
  set a : ℝ := Real.log 2 / L with ha
  have hapos : 0 < a := by positivity
  have hale : a ≤ 1 := by
    rw [ha, div_le_one hL]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hamem : a ∈ Ioc (0 : ℝ) 1 := ⟨hapos, hale⟩
  have hone : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
  have hint := intervalIntegrable_rDiv (M := M) hA hr hb
  rw [primeBoundaryDefect_eq hx2 hr hr' hint]
  -- the five terms
  have hjx : jetWeight r L x = r 1 / (x * L) := by
    rw [jetWeight, hLx, div_self hL.ne']
  have hr1 : |r 1| ≤ A := by
    have h := hb 1 hone
    simpa using h
  have htheta : |Chebyshev.theta x - x| ≤ |C| * (x * Real.exp (-c * Real.sqrt L)) := by
    have h1 : ‖(Chebyshev.theta - id : ℝ → ℝ) x‖
        ≤ C * ‖x * Real.exp (-c * Real.sqrt (Real.log x))‖ := (hT x hxT).1
    have h2 : ‖x * Real.exp (-c * Real.sqrt (Real.log x))‖
        = x * Real.exp (-c * Real.sqrt L) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hLx]
    have h3 : ‖(Chebyshev.theta - id : ℝ → ℝ) x‖ = |Chebyshev.theta x - x| := by
      simp [Real.norm_eq_abs]
    rw [h2, h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hexpK : Real.exp (-c * Real.sqrt L) ≤ K / L ^ (M + 1) := by
    have h := exp_neg_sqrt_le_pow hc0 (M + 1) hL
    rwa [hK, div_div]
  have h1 : |jetWeight r L x * (Chebyshev.theta x - x)| ≤ A * (|C| * K) / L ^ (M + 1) := by
    rw [hjx, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x * L)]
    have hstep : |r 1| / (x * L) * |Chebyshev.theta x - x|
        ≤ (A / (x * L)) * (|C| * (x * Real.exp (-c * Real.sqrt L))) := by
      refine mul_le_mul (by gcongr) htheta (abs_nonneg _) (by positivity)
    refine hstep.trans ?_
    have heq : (A / (x * L)) * (|C| * (x * Real.exp (-c * Real.sqrt L)))
        = A * |C| * Real.exp (-c * Real.sqrt L) / L := by
      field_simp
    rw [heq]
    have hstep2 : A * |C| * Real.exp (-c * Real.sqrt L) / L
        ≤ A * |C| * (K / L ^ (M + 1)) / L := by
      gcongr
    refine hstep2.trans ?_
    have heq2 : A * |C| * (K / L ^ (M + 1)) / L = A * (|C| * K) / (L ^ (M + 1) * L) := by
      field_simp
    rw [heq2]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    calc L ^ (M + 1) = L ^ (M + 1) * 1 := (mul_one _).symm
      _ ≤ L ^ (M + 1) * L := by gcongr
  have hj2 : jetWeight r L 2 = r a / (2 * Real.log 2) := by
    rw [jetWeight, ha]
  have hra : |r a| ≤ A * (Real.log 2) ^ (M + 1) / L ^ (M + 1) := by
    have h := hb a hamem
    rw [ha, div_pow] at h
    calc |r a| ≤ A * ((Real.log 2) ^ (M + 1) / L ^ (M + 1)) := h
      _ = A * (Real.log 2) ^ (M + 1) / L ^ (M + 1) := by ring
  have h2 : |jetWeight r L 2 * (2 - Chebyshev.theta 2)|
      ≤ A * ((Real.log 2) ^ (M + 1) * |2 - Chebyshev.theta 2| / (2 * Real.log 2))
        / L ^ (M + 1) := by
    rw [hj2, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.log 2)]
    have hstep : |r a| / (2 * Real.log 2) * |2 - Chebyshev.theta 2|
        ≤ (A * (Real.log 2) ^ (M + 1) / L ^ (M + 1)) / (2 * Real.log 2)
          * |2 - Chebyshev.theta 2| := by
      gcongr
    refine hstep.trans_eq ?_
    field_simp
  have h3 : |r a / 2| ≤ A * ((Real.log 2) ^ (M + 1) / 2) / L ^ (M + 1) := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hstep : |r a| / 2 ≤ (A * (Real.log 2) ^ (M + 1) / L ^ (M + 1)) / 2 := by gcongr
    refine hstep.trans_eq ?_
    field_simp
  have h4 : |∫ u in (0 : ℝ)..a, r u / u|
      ≤ A * ((Real.log 2) ^ (M + 1) / ((M : ℝ) + 1)) / L ^ (M + 1) := by
    have hbound : ∀ u ∈ Ioc (0 : ℝ) a, |r u / u| ≤ A * u ^ M := by
      intro u hu
      have humem : u ∈ Ioc (0 : ℝ) 1 := ⟨hu.1, le_trans hu.2 hale⟩
      have hupos : (0 : ℝ) < u := hu.1
      rw [abs_div, abs_of_pos hupos, div_le_iff₀ hupos]
      calc |r u| ≤ A * u ^ (M + 1) := hb u humem
        _ = A * u ^ M * u := by ring
    have hI1 : IntervalIntegrable (fun u : ℝ => |r u / u|) volume 0 a := by
      refine (hint.mono_set ?_).abs
      rw [uIcc_of_le hapos.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc le_rfl hale
    have hI2 : IntervalIntegrable (fun u : ℝ => A * u ^ M) volume 0 a :=
      ((intervalIntegral.intervalIntegrable_pow M).const_mul A)
    have hle : |∫ u in (0 : ℝ)..a, r u / u| ≤ ∫ u in (0 : ℝ)..a, A * u ^ M := by
      refine (intervalIntegral.abs_integral_le_integral_abs hapos.le).trans ?_
      refine intervalIntegral.integral_mono_on hapos.le hI1 hI2 ?_
      intro u hu
      rcases eq_or_lt_of_le hu.1 with h | h
      · simp [← h]
        positivity
      · exact hbound u ⟨h, hu.2⟩
    have hval : (∫ u in (0 : ℝ)..a, A * u ^ M) = A * a ^ (M + 1) / ((M : ℝ) + 1) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring_nf
    rw [hval] at hle
    refine hle.trans_eq ?_
    rw [ha, div_pow]
    field_simp
  have h5 : |∫ t in Ioc (2 : ℝ) x, derivJetWeight r r' L t * t * thetaError t|
      ≤ A * B₅ / L ^ (M + 1) := by
    have hptbound : ∀ t ∈ Ioc (2 : ℝ) x,
        ‖derivJetWeight r r' L t * t * thetaError t‖
          ≤ (A / L ^ (M + 1)) * jetTailWeight M t := by
      intro t ht
      have ht2 : (2 : ℝ) < t := ht.1
      have htx : t ≤ x := ht.2
      have htpos : (0 : ℝ) < t := by linarith
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
      have humem : Real.log t / L ∈ Ioc (0 : ℝ) 1 := by
        refine ⟨by positivity, ?_⟩
        rw [div_le_one hL, ← hLx]
        exact Real.log_le_log (by linarith) htx
      have hru : |r (Real.log t / L)| ≤ A * (Real.log t) ^ (M + 1) / L ^ (M + 1) := by
        have h := hb _ humem
        rw [div_pow] at h
        calc |r (Real.log t / L)| ≤ A * ((Real.log t) ^ (M + 1) / L ^ (M + 1)) := h
          _ = A * (Real.log t) ^ (M + 1) / L ^ (M + 1) := by ring
      have hru' : |r' (Real.log t / L)| ≤ A * (Real.log t) ^ M / L ^ M := by
        have h := hb' _ humem
        rw [div_pow] at h
        calc |r' (Real.log t / L)| ≤ A * ((Real.log t) ^ M / L ^ M) := h
          _ = A * (Real.log t) ^ M / L ^ M := by ring
      have hlogge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) (by linarith)
      have hkap : 1 / Real.log t ≤ 1 / Real.log 2 := by
        exact one_div_le_one_div_of_le hlog2 hlogge
      have hkey : |derivJetWeight r r' L t * t|
          ≤ (A / L ^ (M + 1)) *
            (((1 / Real.log 2) * (Real.log t) ^ M
              + ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1)) / t) := by
        have hval : derivJetWeight r r' L t * t
            = r' (Real.log t / L) / (L * t * Real.log t)
              - r (Real.log t / L) * (Real.log t + 1) / (t * Real.log t ^ 2) := by
          rw [derivJetWeight]
          field_simp
        have hb1 : |r' (Real.log t / L) / (L * t * Real.log t)|
            ≤ (A / L ^ (M + 1)) * ((1 / Real.log 2) * (Real.log t) ^ M / t) := by
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < L * t * Real.log t),
            div_le_iff₀ (by positivity : (0 : ℝ) < L * t * Real.log t)]
          have htarget : (A / L ^ (M + 1)) * ((1 / Real.log 2) * (Real.log t) ^ M / t)
              * (L * t * Real.log t)
              = (A * (Real.log t) ^ M / L ^ M) * (Real.log t / Real.log 2) := by
            field_simp
            ring
          rw [htarget]
          have hge1 : (1 : ℝ) ≤ Real.log t / Real.log 2 := by
            rw [le_div_iff₀ hlog2]
            linarith
          have hnn : (0 : ℝ) ≤ A * (Real.log t) ^ M / L ^ M := by positivity
          calc |r' (Real.log t / L)| ≤ A * (Real.log t) ^ M / L ^ M := hru'
            _ = (A * (Real.log t) ^ M / L ^ M) * 1 := (mul_one _).symm
            _ ≤ (A * (Real.log t) ^ M / L ^ M) * (Real.log t / Real.log 2) := by
                exact mul_le_mul_of_nonneg_left hge1 hnn
        have hb2 : |r (Real.log t / L) * (Real.log t + 1) / (t * Real.log t ^ 2)|
            ≤ (A / L ^ (M + 1)) *
              (((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1) / t) := by
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t * Real.log t ^ 2), abs_mul,
            abs_of_pos (by linarith : (0 : ℝ) < Real.log t + 1),
            div_le_iff₀ (by positivity : (0 : ℝ) < t * Real.log t ^ 2)]
          have htarget : (A / L ^ (M + 1)) *
              (((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1) / t)
              * (t * Real.log t ^ 2)
              = (A * (Real.log t) ^ (M + 1) / L ^ (M + 1)) *
                (((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * Real.log t ^ 2) := by
            field_simp
          rw [htarget]
          have hnn : (0 : ℝ) ≤ A * (Real.log t) ^ (M + 1) / L ^ (M + 1) := by positivity
          have hcomp : Real.log t + 1
              ≤ ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * Real.log t ^ 2 := by
            have h1 : Real.log t ≤ (1 / Real.log 2) * Real.log t ^ 2 := by
              rw [one_div, inv_mul_eq_div, le_div_iff₀ hlog2]
              nlinarith
            have h2 : (1 : ℝ) ≤ (1 / Real.log 2) ^ 2 * Real.log t ^ 2 := by
              have : (1 : ℝ) ≤ (Real.log t / Real.log 2) ^ 2 := by
                have hge1 : (1 : ℝ) ≤ Real.log t / Real.log 2 := by
                  rw [le_div_iff₀ hlog2]
                  linarith
                nlinarith
              calc (1 : ℝ) ≤ (Real.log t / Real.log 2) ^ 2 := this
                _ = (1 / Real.log 2) ^ 2 * Real.log t ^ 2 := by
                    field_simp
            nlinarith
          calc |r (Real.log t / L)| * (Real.log t + 1)
              ≤ (A * (Real.log t) ^ (M + 1) / L ^ (M + 1)) * (Real.log t + 1) := by
                exact mul_le_mul_of_nonneg_right hru (by linarith)
            _ ≤ (A * (Real.log t) ^ (M + 1) / L ^ (M + 1)) *
                (((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * Real.log t ^ 2) := by
                exact mul_le_mul_of_nonneg_left hcomp hnn
        rw [hval]
        have htri : |r' (Real.log t / L) / (L * t * Real.log t)
            - r (Real.log t / L) * (Real.log t + 1) / (t * Real.log t ^ 2)|
            ≤ |r' (Real.log t / L) / (L * t * Real.log t)|
              + |r (Real.log t / L) * (Real.log t + 1) / (t * Real.log t ^ 2)| := by
          rw [sub_eq_add_neg]
          refine (abs_add_le _ _).trans_eq ?_
          rw [abs_neg]
        refine htri.trans ?_
        have hsum := add_le_add hb1 hb2
        refine hsum.trans_eq ?_
        ring
      calc ‖derivJetWeight r r' L t * t * thetaError t‖
          = |derivJetWeight r r' L t * t| * |thetaError t| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ ((A / L ^ (M + 1)) *
              (((1 / Real.log 2) * (Real.log t) ^ M
                + ((1 / Real.log 2) + (1 / Real.log 2) ^ 2) * (Real.log t) ^ (M + 1)) / t))
              * |thetaError t| := by
            exact mul_le_mul_of_nonneg_right hkey (abs_nonneg _)
        _ = (A / L ^ (M + 1)) * jetTailWeight M t := by
            rw [jetTailWeight]
            ring
    have hintg : IntegrableOn (fun t : ℝ => (A / L ^ (M + 1)) * jetTailWeight M t)
        (Ioc (2 : ℝ) x) :=
      ((integrableOn_jetTailWeight M).mono_set Ioc_subset_Ioi_self).const_mul _
    have hnorm : ‖∫ t in Ioc (2 : ℝ) x, derivJetWeight r r' L t * t * thetaError t‖
        ≤ ∫ t in Ioc (2 : ℝ) x, (A / L ^ (M + 1)) * jetTailWeight M t := by
      refine MeasureTheory.norm_integral_le_of_norm_le hintg ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hptbound t ht
    rw [Real.norm_eq_abs] at hnorm
    refine hnorm.trans ?_
    rw [integral_const_mul]
    have hmono : (∫ t in Ioc (2 : ℝ) x, jetTailWeight M t) ≤ B₅ := by
      rw [hB5]
      refine setIntegral_mono_set (integrableOn_jetTailWeight M) ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact jetTailWeight_nonneg M ht
      · exact LE.le.eventuallyLE Ioc_subset_Ioi_self
    have hstep : A / L ^ (M + 1) * (∫ t in Ioc (2 : ℝ) x, jetTailWeight M t)
        ≤ A / L ^ (M + 1) * B₅ := by
      refine mul_le_mul_of_nonneg_left hmono (by positivity)
    refine hstep.trans_eq ?_
    field_simp
  -- assemble
  have htri : |jetWeight r L x * (Chebyshev.theta x - x)
      + jetWeight r L 2 * (2 - Chebyshev.theta 2)
      + r (Real.log 2 / Real.log x) / 2
      - (∫ u in (0 : ℝ)..(Real.log 2 / Real.log x), r u / u)
      - ∫ t in Ioc (2 : ℝ) x, derivJetWeight r r' (Real.log x) t * t * thetaError t|
      ≤ |jetWeight r L x * (Chebyshev.theta x - x)|
        + |jetWeight r L 2 * (2 - Chebyshev.theta 2)|
        + |r a / 2|
        + |∫ u in (0 : ℝ)..a, r u / u|
        + |∫ t in Ioc (2 : ℝ) x, derivJetWeight r r' L t * t * thetaError t| := by
    have e1 : ∀ X Y : ℝ, |X - Y| ≤ |X| + |Y| := by
      intro X Y
      rw [sub_eq_add_neg]
      refine (abs_add_le _ _).trans_eq ?_
      rw [abs_neg]
    have e2 : ∀ X Y : ℝ, |X + Y| ≤ |X| + |Y| := fun X Y => abs_add_le X Y
    have s1 := e1 (jetWeight r L x * (Chebyshev.theta x - x)
      + jetWeight r L 2 * (2 - Chebyshev.theta 2) + r a / 2
      - (∫ u in (0 : ℝ)..a, r u / u))
      (∫ t in Ioc (2 : ℝ) x, derivJetWeight r r' L t * t * thetaError t)
    have s2 := e1 (jetWeight r L x * (Chebyshev.theta x - x)
      + jetWeight r L 2 * (2 - Chebyshev.theta 2) + r a / 2)
      (∫ u in (0 : ℝ)..a, r u / u)
    have s3 := e2 (jetWeight r L x * (Chebyshev.theta x - x)
      + jetWeight r L 2 * (2 - Chebyshev.theta 2)) (r a / 2)
    have s4 := e2 (jetWeight r L x * (Chebyshev.theta x - x))
      (jetWeight r L 2 * (2 - Chebyshev.theta 2))
    rw [← ha, ← hLdef]
    linarith
  refine htri.trans ?_
  have hsum : |jetWeight r L x * (Chebyshev.theta x - x)|
      + |jetWeight r L 2 * (2 - Chebyshev.theta 2)|
      + |r a / 2|
      + |∫ u in (0 : ℝ)..a, r u / u|
      + |∫ t in Ioc (2 : ℝ) x, derivJetWeight r r' L t * t * thetaError t|
      ≤ A * (|C| * K) / L ^ (M + 1)
        + A * ((Real.log 2) ^ (M + 1) * |2 - Chebyshev.theta 2| / (2 * Real.log 2)) / L ^ (M + 1)
        + A * ((Real.log 2) ^ (M + 1) / 2) / L ^ (M + 1)
        + A * ((Real.log 2) ^ (M + 1) / ((M : ℝ) + 1)) / L ^ (M + 1)
        + A * B₅ / L ^ (M + 1) := by
    linarith
  refine hsum.trans_eq ?_
  field_simp

end

end RHTower
