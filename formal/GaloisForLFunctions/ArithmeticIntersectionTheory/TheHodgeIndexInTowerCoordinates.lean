import GaloisForLFunctions.ArithmeticIntersectionTheory.ThePolarPartPairsThePoleDirection
import GaloisForLFunctions.RHTower.WeilArchimedeanExactForm

/-!
# The Hodge index in tower coordinates

On a log-atom test `f = Σ_{n ∈ S} x_n φ(· − log n)` every part of Weil's explicit formula is now an
explicit form on the cycle `x`. The prime part is `‖φ‖² Σ_p Q_p(x)`
(`WeilsPrimeFunctionalIsTheFiniteIntersection`); this module computes the archimedean and polar part
from the exact archimedean form `A(h) = γ₀ h(0) + ∫_0^∞ [(h(0) − h(y)) e^{y/2}/sinh y + 4h(y) cosh(y/2)] dy`
(RHTower `weilArchRe_eq_exactForm`), `h` the autocorrelation of `f`.

* **Autocorrelation of a log-atom test** (`autocorr_logAtom`): `h(y) = Σ_{m,n} x_m x_n Φ(y + log m − log n)`
  with `Φ` the autocorrelation of `φ`. Separation leaves `h(0) = Φ(0)|x|²` and, for `y > 0`, only the
  pairs `m ≤ n`.
* **The archimedean part in tower coordinates** (`weilArchRe_logAtom`):

      Re(archimedean + polar part) = E_φ |x|² + 2αβ (Σ x_n n^{−1/2})(Σ x_n n^{1/2}) − Σ_{m<n} x_m x_n K_φ(log(n/m)),

  with the **self-energy of the atom** `E_φ = γ₀ Φ(0) + ∫_0^∞ (Φ(0) − Φ(y)) e^{y/2}/sinh y dy`
  (`atomSelfEnergy`), the **archimedean kernel** `K_φ(c) = ∫_0^∞ Φ(y − c) e^{y/2}/sinh y dy`
  (`archKernel`) and `α, β` the Mellin values of `φ` at `∓½`.
* **RH in tower coordinates** (`riemannHypothesis_tower_inequality`): under RH, for every log-atom cycle,

      ‖φ‖² Σ_p Q_p(x) + Σ_{m<n} x_m x_n K_φ(log(n/m)) ≤ E_φ |x|² + 2αβ (Σ x_n n^{−1/2})(Σ x_n n^{1/2}).

The left side is the finite intersection (the transverse towers) plus the archimedean coupling of
distinct atoms; the right side is the self-energy of the atoms plus the polar pairing of the pole
direction. This is the Hodge index of the explicit formula written as one inequality between
explicit forms on `ℓ²(⊕_p ℕ)`.
-/

noncomputable section

open MeasureTheory Set Finset Complex
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory RHTower.ArchimedeanAnomaly

variable {φ : ℝ → ℝ} {δ : ℝ}

/-- The archimedean jump weight `e^{y/2}/sinh y`. -/
def jumpWeight (y : ℝ) : ℝ := Real.exp (y / 2) / Real.sinh y

/-- The **self-energy of an atom**: `E_φ = γ₀ Φ(0) + ∫_0^∞ (Φ(0) − Φ(y)) e^{y/2}/sinh y dy`. -/
def atomSelfEnergy (φ : ℝ → ℝ) : ℝ :=
  Zeta23.EF.gammaBracket 0 * autocorr φ 0 +
    ∫ y in Ioi 0, (autocorr φ 0 - autocorr φ y) * jumpWeight y

/-- The **archimedean kernel** at lag `c`: `K_φ(c) = ∫_0^∞ Φ(y − c) e^{y/2}/sinh y dy`. -/
def archKernel (φ : ℝ → ℝ) (c : ℝ) : ℝ := ∫ y in Ioi 0, autocorr φ (y - c) * jumpWeight y

theorem continuousOn_jumpWeight : ContinuousOn jumpWeight (Ioi 0) :=
  (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.div
    Real.continuous_sinh.continuousOn fun y hy => (Real.sinh_pos_iff.mpr hy).ne'

/-- The jump integrand of a `C²_c` test is integrable on `(0, ∞)`. -/
theorem integrableOn_jump {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun y => (autocorr g 0 - autocorr g y) * jumpWeight y) (Ioi 0) := by
  have hc : Continuous (autocorr g) := RHTower.ArchimedeanExactForm.continuous_autocorr hg hgc
  have hnn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ (autocorr g 0 - autocorr g y) * jumpWeight y := by
    intro y hy
    have hsq := integral_sub_shift_sq hgc hg.continuous y
    have h0 : 0 ≤ ∫ u, (g u - g (u + y)) ^ 2 := integral_nonneg fun u => sq_nonneg _
    exact mul_nonneg (by linarith) (div_nonneg (Real.exp_pos _).le
      (Real.sinh_pos_iff.mpr hy).le)
  have hlev : (∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y * ∫ u, (g u - g (u + y)) ^ 2)) =
      ∫⁻ y in Ioi 0, ENNReal.ofReal ((autocorr g 0 - autocorr g y) * jumpWeight y) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [integral_sub_shift_sq hgc hg.continuous y, jumpWeight, exp_half_div_sinh_eq hy]
    congr 1
    ring
  have hfin := RHTower.WeilMarkovPole.lintegral_levy_ne_top hg hgc
  rw [hlev] at hfin
  refine ⟨ContinuousOn.aestronglyMeasurable ((continuousOn_const.sub hc.continuousOn).mul
    continuousOn_jumpWeight) measurableSet_Ioi, ?_⟩
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt (le_of_eq ?_) hfin.lt_top
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [Real.enorm_eq_ofReal (hnn y hy)]

/-- `Φ(z) = 0` for `|z| > δ`. -/
theorem autocorr_eq_zero_of_lt (hφs : ∀ u, δ / 2 < |u| → φ u = 0) {z : ℝ} (hz : δ < |z|) :
    autocorr φ z = 0 := by
  unfold autocorr
  have : (fun u => φ u * φ (u + z)) = fun _ => 0 := by
    funext u
    have h := RHTower.SeparatedBump.mul_translate_eq_zero hφs (p := 0) (q := -z)
      (by rw [zero_sub, abs_neg]; exact hz) u
    simpa [sub_neg_eq_add] using h
  rw [this, integral_zero]

/-- A lag `y − c` with `c > δ` gives an integrable archimedean coupling on `(0, ∞)`. -/
theorem integrableOn_coupling (hφ : ContDiff ℝ 2 φ) (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    (hφc : HasCompactSupport φ) {c : ℝ} (hc : δ < c) :
    IntegrableOn (fun y => autocorr φ (y - c) * jumpWeight y) (Ioi 0) := by
  have hcont : Continuous (autocorr φ) := RHTower.ArchimedeanExactForm.continuous_autocorr hφ hφc
  have hIcc : IntegrableOn (fun y => autocorr φ (y - c) * jumpWeight y) (Icc (c - δ) (c + δ)) := by
    refine ContinuousOn.integrableOn_Icc ((hcont.comp (continuous_id.sub continuous_const)).continuousOn.mul
      (continuousOn_jumpWeight.mono fun y hy => ?_))
    exact lt_of_lt_of_le (by linarith) hy.1
  refine hIcc.of_forall_diff_eq_zero measurableSet_Ioi fun y hy => ?_
  have hy' : δ < |y - c| := by
    rcases hy with ⟨-, hy⟩
    simp only [mem_Icc, not_and_or, not_le] at hy
    rcases hy with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [autocorr_eq_zero_of_lt hφs hy', zero_mul]

/-- **The autocorrelation of a log-atom test**: `h(y) = Σ_{m,n} x_m x_n Φ(y + log m − log n)`. -/
theorem autocorr_logAtom (hφ : ContDiff ℝ 2 φ) (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    (S : Finset ℕ) (x : ℕ → ℝ) (y : ℝ) :
    autocorr (logAtomTest φ S x) y =
      ∑ m ∈ S, ∑ n ∈ S, x m * x n * autocorr φ (y + Real.log m - Real.log n) := by
  have e : ∀ u, logAtomTest φ S x u * logAtomTest φ S x (u + y) = ∑ m ∈ S, ∑ n ∈ S,
      x m * x n * (φ (u - Real.log m) * φ (u - (Real.log n - y))) := fun u => by
    unfold logAtomTest
    rw [sum_mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    rw [show u + y - Real.log n = u - (Real.log n - y) by ring]
    ring
  unfold autocorr
  simp_rw [e]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    (RHTower.SeparatedBump.integrable_translate_mul_translate hφ hφs _ _).const_mul _]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ =>
    (RHTower.SeparatedBump.integrable_translate_mul_translate hφ hφs _ _).const_mul _]
  refine sum_congr rfl fun n _ => ?_
  rw [integral_const_mul]
  congr 1
  rw [← integral_add_right_eq_self (fun u => φ (u - Real.log m) * φ (u - (Real.log n - y)))
    (Real.log m)]
  congr 1; funext v
  rw [show v + Real.log m - Real.log m = v by ring,
    show v + Real.log m - (Real.log n - y) = v + (y + Real.log m - Real.log n) by ring]

/-- Distinct orders of a log-atom set are farther apart than the atoms are wide. -/
theorem lt_abs_log_sub_log {S : Finset ℕ} {M : ℕ} (hd : LogAtomData φ δ S M) {m n : ℕ}
    (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n) : δ < |Real.log m - Real.log n| := by
  by_contra h
  push Not at h
  apply hmn
  have := eq_of_abs_log_sub_lt (k := 1) one_pos (hd.pos m hm) (hd.pos n hn) (hd.le m hm)
    (by rw [Nat.cast_one, Real.log_one, zero_sub, abs_neg]; exact h.trans_lt hd.narrow)
  rw [one_mul] at this
  exact this.symm

/-- `h(0) = Φ(0) |x|²`. -/
theorem autocorr_logAtom_zero {S : Finset ℕ} {M : ℕ} (hd : LogAtomData φ δ S M) (x : ℕ → ℝ) :
    autocorr (logAtomTest φ S x) 0 = autocorr φ 0 * ∑ n ∈ S, x n ^ 2 := by
  rw [autocorr_logAtom hd.contDiff hd.support, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [← add_sum_erase _ _ hm, sum_eq_zero fun n hn => by
    rw [autocorr_eq_zero_of_lt hd.support (by
      rw [zero_add]; exact lt_abs_log_sub_log hd hm (mem_of_mem_erase hn) (ne_of_mem_erase hn).symm),
      mul_zero]]
  simp only [zero_add, sub_self, add_zero]
  ring

/-- For `y > 0` only the pairs `m ≤ n` contribute. -/
theorem autocorr_logAtom_pos {S : Finset ℕ} {M : ℕ} (hd : LogAtomData φ δ S M) (x : ℕ → ℝ)
    {y : ℝ} (hy : 0 < y) :
    autocorr (logAtomTest φ S x) y = autocorr φ y * ∑ n ∈ S, x n ^ 2 +
      ∑ m ∈ S, ∑ n ∈ S, (if m < n then x m * x n * autocorr φ (y - (Real.log n - Real.log m))
        else 0) := by
  rw [autocorr_logAtom hd.contDiff hd.support, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun m hm => ?_
  rw [← add_sum_erase _ _ hm, ← add_sum_erase (S) (fun n => if m < n then _ else 0) hm,
    if_neg (lt_irrefl m)]
  simp only [add_sub_cancel_right, add_zero]
  rw [show x m * x m * autocorr φ y = autocorr φ y * x m ^ 2 by ring]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  have hn' := mem_of_mem_erase hn
  have hne := ne_of_mem_erase hn
  split_ifs with hlt
  · rw [show y + Real.log m - Real.log n = y - (Real.log n - Real.log m) by ring]
  · have hgt : n < m := lt_of_le_of_ne (not_lt.mp hlt) hne
    have hlog : Real.log n < Real.log m :=
      Real.log_lt_log (by exact_mod_cast hd.pos n hn') (by exact_mod_cast hgt)
    have hsep := lt_abs_log_sub_log hd hm hn' hne.symm
    rw [abs_of_pos (by linarith)] at hsep
    rw [autocorr_eq_zero_of_lt hd.support (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]

/-- Each archimedean coupling term of a log-atom test is integrable on `(0, ∞)`. -/
theorem integrableOn_pairTerm {S : Finset ℕ} {M : ℕ} (hd : LogAtomData φ δ S M) (x : ℕ → ℝ)
    {m n : ℕ} (hm : m ∈ S) (hn : n ∈ S) :
    IntegrableOn (fun y => if m < n then x m * x n *
      (autocorr φ (y - (Real.log n - Real.log m)) * jumpWeight y) else 0) (Ioi 0) := by
  split_ifs with hlt
  · have hlog : Real.log m < Real.log n :=
      Real.log_lt_log (by exact_mod_cast hd.pos m hm) (by exact_mod_cast hlt)
    have hsep := lt_abs_log_sub_log hd hn hm hlt.ne'
    rw [abs_of_pos (by linarith)] at hsep
    exact (integrableOn_coupling hd.contDiff hd.support
      (RHTower.SeparatedBump.hasCompactSupport_of_abs hd.support) hsep).const_mul _
  · exact integrableOn_zero

/-- **The archimedean and polar part in tower coordinates.** -/
theorem weilArchRe_logAtom {S : Finset ℕ} {M : ℕ} (hd : LogAtomData φ δ S M) (x : ℕ → ℝ) :
    RHTower.WeilOneSided.weilArchRe (Zeta23.EF.weilTest (fun u => (logAtomTest φ S x u : ℂ))
      (fun u => (logAtomTest φ S x u : ℂ))) =
      atomSelfEnergy φ * ∑ n ∈ S, x n ^ 2 +
        2 * (∫ v, φ v * Real.exp (-1 / 2 * v)) * (∫ v, φ v * Real.exp (1 / 2 * v)) *
          (∑ n ∈ S, x n / Real.sqrt n) * (∑ n ∈ S, x n * Real.sqrt n) -
        ∑ m ∈ S, ∑ n ∈ S, (if m < n then x m * x n * archKernel φ (Real.log n - Real.log m)
          else 0) := by
  set f := logAtomTest φ S x
  have hf : ContDiff ℝ 2 f := contDiff_logAtomTest hd.contDiff S x
  have hfc : HasCompactSupport f := hasCompactSupport_logAtomTest hd.support S x
  have hφc : HasCompactSupport φ := RHTower.SeparatedBump.hasCompactSupport_of_abs hd.support
  rw [RHTower.ArchimedeanExactForm.weilArchRe_eq_exactForm hf hfc]
  -- split the integral into the jump and the pole
  have hJ := integrableOn_jump hf hfc
  have hcf : Continuous (autocorr f) := RHTower.ArchimedeanExactForm.continuous_autocorr hf hfc
  have hcsf : HasCompactSupport (autocorr f) :=
    RHTower.ArchimedeanExactForm.hasCompactSupport_autocorr hfc
  have hP : Integrable fun y => 4 * autocorr f y * Real.cosh (y / 2) :=
    ((continuous_const.mul hcf).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hcsf.mul_left.mul_right)
  rw [integral_add hJ hP.integrableOn]
  -- the pole: `4 ∫_0^∞ h cosh = 2 (∫ f e^{u/2})(∫ f e^{−u/2})`
  have hpole : ∫ y in Ioi 0, 4 * autocorr f y * Real.cosh (y / 2) =
      2 * (∫ v, φ v * Real.exp (-1 / 2 * v)) * (∫ v, φ v * Real.exp (1 / 2 * v)) *
        (∑ n ∈ S, x n / Real.sqrt n) * (∑ n ∈ S, x n * Real.sqrt n) := by
    have heven : ∀ y, autocorr f y * Real.cosh (y / 2) = autocorr f |y| * Real.cosh (|y| / 2) := by
      intro y
      rcases le_or_gt 0 y with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, RHTower.ArchimedeanExactForm.autocorr_neg, neg_div, Real.cosh_neg]
    have hfull := RHTower.ArchimedeanExactForm.integral_autocorr_mul_cosh hf hfc
    rw [funext heven, integral_comp_abs (f := fun y => autocorr f y * Real.cosh (y / 2))] at hfull
    have h1 := integral_logAtom_mul_exp hd.contDiff hd.support S x (1 / 2)
    have h2 := integral_logAtom_mul_exp hd.contDiff hd.support S x (-1 / 2)
    have e1 : (∫ u, f u * Real.exp (u / 2)) = (∑ n ∈ S, x n * Real.sqrt n) *
        ∫ v, φ v * Real.exp (1 / 2 * v) := by
      rw [show (fun u => f u * Real.exp (u / 2)) = fun u => f u * Real.exp (1 / 2 * u) from
        funext fun u => by ring_nf, h1]
      congr 1
      exact sum_congr rfl fun n hn => by rw [exp_half_log (hd.pos n hn)]
    have e2 : (∫ u, f u * Real.exp (-u / 2)) = (∑ n ∈ S, x n / Real.sqrt n) *
        ∫ v, φ v * Real.exp (-1 / 2 * v) := by
      rw [show (fun u => f u * Real.exp (-u / 2)) = fun u => f u * Real.exp (-1 / 2 * u) from
        funext fun u => by ring_nf, h2]
      congr 1
      exact sum_congr rfl fun n hn => by rw [exp_neg_half_log (hd.pos n hn), mul_one_div]
    rw [e1, e2] at hfull
    have : ∫ y in Ioi 0, 4 * autocorr f y * Real.cosh (y / 2) =
        2 * (2 * ∫ y in Ioi 0, autocorr f y * Real.cosh (y / 2)) := by
      rw [← integral_const_mul, ← integral_const_mul]
      congr 1; funext y; ring
    rw [this, ← hfull]
    ring
  -- the jump, pair by pair
  have hjump : ∫ y in Ioi 0, (autocorr f 0 - autocorr f y) * (Real.exp (y / 2) / Real.sinh y) =
      (∑ n ∈ S, x n ^ 2) * ∫ y in Ioi 0, (autocorr φ 0 - autocorr φ y) * jumpWeight y -
        ∑ m ∈ S, ∑ n ∈ S, (if m < n then x m * x n * archKernel φ (Real.log n - Real.log m)
          else 0) := by
    have hpt : ∀ y ∈ Ioi (0 : ℝ), (autocorr f 0 - autocorr f y) * (Real.exp (y / 2) / Real.sinh y) =
        (∑ n ∈ S, x n ^ 2) * ((autocorr φ 0 - autocorr φ y) * jumpWeight y) -
          ∑ m ∈ S, ∑ n ∈ S, (if m < n then x m * x n *
            (autocorr φ (y - (Real.log n - Real.log m)) * jumpWeight y) else 0) := by
      intro y hy
      have e : (∑ m ∈ S, ∑ n ∈ S, (if m < n then x m * x n *
          autocorr φ (y - (Real.log n - Real.log m)) else 0)) * jumpWeight y =
          ∑ m ∈ S, ∑ n ∈ S, (if m < n then x m * x n *
            (autocorr φ (y - (Real.log n - Real.log m)) * jumpWeight y) else 0) := by
        rw [sum_mul]
        refine sum_congr rfl fun m _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun n _ => ?_
        split_ifs <;> ring
      rw [autocorr_logAtom_zero hd, autocorr_logAtom_pos hd x hy, ← e]
      simp only [jumpWeight]
      ring
    have hφjump := integrableOn_jump hd.contDiff hφc
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub (hφjump.const_mul _)
      (integrable_finsetSum _ fun m hm => integrable_finsetSum _ fun n hn =>
        integrableOn_pairTerm hd x hm hn),
      integral_const_mul, integral_finsetSum _ fun m hm => integrable_finsetSum _ fun n hn =>
        integrableOn_pairTerm hd x hm hn]
    congr 1
    refine sum_congr rfl fun m hm => ?_
    rw [integral_finsetSum _ fun n hn => integrableOn_pairTerm hd x hm hn]
    refine sum_congr rfl fun n _ => ?_
    split_ifs
    · rw [integral_const_mul, archKernel]
    · simp
  rw [autocorr_logAtom_zero hd, hjump, hpole, atomSelfEnergy]
  ring

end GaloisForLFunctions.ArithmeticIntersectionTheory
