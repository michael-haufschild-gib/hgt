import GaloisForLFunctions.RHTower.LiouvilleTwistedDensityPhase
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# Prime-phase capacity of the full Liouville twist

Two disjoint fixed intervals carry a uniform angular defect of the actual exponential
density. The ordinary PNT gives reciprocal prime mass of order `1 / log T` in each.
The exact finite pairwise triangle-deficit identity then yields a uniform positive
lower bound for `log T` times the difference between the full phase capacity and the
norm of the full linear response. Every selected prime and every pair is retained.

The final existence theorem has no arithmetic or analytic premises. Its coefficients
are the unrestricted responses `F(p/T)/p`. Transferring this surplus to the exact
band-free cofactor coefficients still requires their full error estimate. This is the
capacity component of MC-C12.92, not a simple-zero theorem, a critical Liouville bound,
or an RH proof.
-/

open Filter Finset
open scoped Topology BigOperators

namespace RHTower.LiouvilleTwistedDensity
noncomputable section

/-- The nonnegative defect in the complex triangle inequality. -/
def phaseDefect (z w : ℂ) : ℝ := ‖z‖ * ‖w‖ - (z * (starRingEnd ℂ) w).re

private theorem phaseDefect_nonneg (z w : ℂ) : 0 ≤ phaseDefect z w := by
  have h := Complex.re_le_norm (z * (starRingEnd ℂ) w)
  rw [norm_mul, Complex.norm_conj] at h
  exact sub_nonneg.mpr h

private theorem phaseDefect_real_mul (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (z w : ℂ) :
    phaseDefect ((r : ℂ) * z) ((s : ℂ) * w) = r * s * phaseDefect z w := by
  simp only [phaseDefect, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, abs_of_nonneg hs, map_mul, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem phaseDefect_sum (P : Finset ℕ) (f : ℕ → ℂ) :
    (∑ p ∈ P, ‖f p‖) ^ 2 - ‖∑ p ∈ P, f p‖ ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, phaseDefect (f p) (f q) := by
  have hnorm : ‖∑ p ∈ P, f p‖ ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, (f p * (starRingEnd ℂ) (f q)).re := by
    have h : ‖∑ p ∈ P, f p‖ ^ 2 =
        ((∑ p ∈ P, f p) * (starRingEnd ℂ) (∑ p ∈ P, f p)).re := by
      rw [Complex.mul_conj, Complex.sq_norm]
      norm_num
    rw [h, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun p _ => Complex.re_sum _ _
  rw [hnorm, pow_two, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => (Finset.sum_sub_distrib _ _).symm

/-- Two separated intervals with a uniform defect for the actual full density. -/
theorem exists_phaseDefect_intervals :
    ∃ a b c d δ : ℝ, 1 < a ∧ a < b ∧ b < c ∧ c < d ∧ 0 < δ ∧
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d,
        δ ≤ phaseDefect (exponentialDensity x) (exponentialDensity y) := by
  let u : ℝ := Real.log 16 + 2
  have hlog : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have hu : 1 < u := by dsimp [u]; linarith
  have huphase : Real.log 16 < u := by dsimp [u]; linarith
  have him : (exponentialDensity u * (starRingEnd ℂ) (exponentialDensity (2 * u))).im ≠ 0 := by
    simpa only [mul_comm] using (exponentialDensity_phase_separation huphase).ne'
  have hD : 0 < phaseDefect (exponentialDensity u) (exponentialDensity (2 * u)) := by
    have h := (le_abs_self _).trans_lt (Complex.abs_re_lt_norm.mpr him)
    simpa only [phaseDefect, norm_mul, Complex.norm_conj] using sub_pos.mpr h
  let A := phaseDefect (exponentialDensity u) (exponentialDensity (2 * u))
  have hFu : ContinuousAt exponentialDensity u := continuousOn_exponentialDensity.continuousAt
    (isOpen_Ioi.mem_nhds (by change 0 < u; linarith))
  have hFv : ContinuousAt exponentialDensity (2 * u) := continuousOn_exponentialDensity.continuousAt
    (isOpen_Ioi.mem_nhds (by change 0 < 2 * u; linarith))
  have hfst : ContinuousAt (fun v : ℝ × ℝ => exponentialDensity v.1) (u, 2 * u) :=
    hFu.comp (f := Prod.fst) (x := (u, 2 * u)) continuous_fst.continuousAt
  have hsnd : ContinuousAt (fun v : ℝ × ℝ => exponentialDensity v.2) (u, 2 * u) :=
    hFv.comp (f := Prod.snd) (x := (u, 2 * u)) continuous_snd.continuousAt
  have hcont : ContinuousAt (fun v : ℝ × ℝ =>
      phaseDefect (exponentialDensity v.1) (exponentialDensity v.2)) (u, 2 * u) :=
    (hfst.norm.mul hsnd.norm).sub (Complex.continuous_re.continuousAt.comp
      (hfst.mul (Complex.continuous_conj.continuousAt.comp hsnd)))
  have hnear : ∀ᶠ v : ℝ × ℝ in 𝓝 (u, 2 * u), A / 2 <
      phaseDefect (exponentialDensity v.1) (exponentialDensity v.2) :=
    hcont.tendsto.eventually (isOpen_Ioi.mem_nhds (by change A / 2 < A; dsimp [A]; linarith))
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let r := min (ρ / 2) ((u - 1) / 4)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hru : r ≤ (u - 1) / 4 := min_le_right _ _
  refine ⟨u-r, u+r, 2*u-r, 2*u+r, A/2,
    by linarith, by linarith, by linarith, by linarith, by dsimp [A]; linarith, ?_⟩
  intro x hx y hy
  apply (hball (y := (x, y)) ?_).le
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact (max_le (abs_le.mpr (by constructor <;> linarith [hx.1, hx.2]))
    (abs_le.mpr (by constructor <;> linarith [hy.1, hy.2]))).trans_lt hrρ

private theorem density_bounded_above_one :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 1 ≤ x → ‖exponentialDensity x‖ ≤ M := by
  let C : ℝ := ∑' n : ℕ, Real.exp (-(n : ℝ))
  have hC : 0 ≤ C := tsum_nonneg fun n => (Real.exp_pos _).le
  refine ⟨C + 1, by linarith, fun x hx => ?_⟩
  have h := GaloisForLFunctions.HTGeometry.norm_coeffLaplaceProfile_le_exp_neg
    norm_coefficient_le_one (by simp [coefficient]) hx
  have hexp : Real.exp (-x) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (by linarith : -x ≤ 0)
  exact h.trans ((mul_le_of_le_one_left hC hexp).trans (by linarith))

/-- All primes in the scaled interval `(a*T,b*T]`. -/
def primeWindow (a b T : ℝ) : Finset ℕ :=
  GaloisForLFunctions.HTGeometry.primesInIoc ⌊a * T⌋₊ ⌊b * T⌋₊

def reciprocalMass (a b T : ℝ) : ℝ := ∑ p ∈ primeWindow a b T, 1 / (p : ℝ)

private theorem mem_primeWindow {a b T : ℝ} (hb : 0 ≤ b * T) {p : ℕ}
    (hp : p ∈ primeWindow a b T) : p.Prime ∧ a * T < (p : ℝ) ∧ (p : ℝ) ≤ b * T := by
  obtain ⟨hpp, hlo, hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  exact ⟨hpp, Nat.lt_of_floor_lt hlo,
    (by exact_mod_cast hhi : (p : ℝ) ≤ (⌊b * T⌋₊ : ℝ)).trans (Nat.floor_le hb)⟩

private theorem scaled_primeCounting_tendsto {a : ℝ} (ha : 1 < a) :
    Tendsto (fun T : ℝ => Real.log T / T * (Nat.primeCounting ⌊a * T⌋₊ : ℝ))
      atTop (𝓝 a) := by
  obtain ⟨c, hc, hpi⟩ := pi_alt
  have hc0 : Tendsto c atTop (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp hc
  have hca : Tendsto (fun T : ℝ => c (a * T)) atTop (𝓝 0) :=
    hc0.comp (tendsto_id.const_mul_atTop (by linarith : 0 < a))
  have hlim : Tendsto (fun T : ℝ => (1 + c (a * T)) * a * (Real.log T / Real.log (a * T)))
      atTop (𝓝 a) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).add hca).mul_const a).mul
      (GaloisForLFunctions.HTGeometry.tendsto_log_dilate_ratio ha)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  rw [hpi]
  have haT : 1 < a * T := by nlinarith
  field_simp [(by linarith : T ≠ 0), (Real.log_pos haT).ne']

private theorem scaled_primeWindow_card_tendsto {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    Tendsto (fun T : ℝ => Real.log T / T * ((primeWindow a b T).card : ℝ))
      atTop (𝓝 (b - a)) := by
  have h := (scaled_primeCounting_tendsto (ha.trans hab)).sub (scaled_primeCounting_tendsto ha)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [primeWindow, GaloisForLFunctions.HTGeometry.card_primesInIoc
    (Nat.floor_mono (mul_le_mul_of_nonneg_right hab.le hT.le))]
  ring

private theorem reciprocalMass_bounds {a b T : ℝ} (ha : 0 < a) (hab : a < b) (hT : 0 < T) :
    ((primeWindow a b T).card : ℝ) / (b * T) ≤ reciprocalMass a b T ∧
      reciprocalMass a b T ≤ ((primeWindow a b T).card : ℝ) / (a * T) := by
  have hb := ha.trans hab
  constructor
  · calc
      _ = ∑ p ∈ primeWindow a b T, 1 / (b * T) := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum fun p hp => by
        obtain ⟨hpp, _, hhi⟩ := mem_primeWindow (mul_nonneg hb.le hT.le) hp
        exact one_div_le_one_div_of_le (by exact_mod_cast hpp.pos) hhi
  · calc
      _ ≤ ∑ p ∈ primeWindow a b T, 1 / (a * T) := Finset.sum_le_sum fun p hp => by
        obtain ⟨_, hlo, _⟩ := mem_primeWindow (mul_nonneg hb.le hT.le) hp
        exact one_div_le_one_div_of_le (mul_pos ha hT) hlo.le
      _ = _ := by simp [div_eq_mul_inv]

private theorem eventual_reciprocalMass_bounds {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    ∃ l u : ℝ, 0 < l ∧ 0 < u ∧ ∀ᶠ T : ℝ in atTop,
      l ≤ Real.log T * reciprocalMass a b T ∧ Real.log T * reciprocalMass a b T ≤ u := by
  let l : ℝ := (b - a) / (2 * b)
  let u : ℝ := (2 * (b - a)) / a
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hcounts := (scaled_primeWindow_card_tendsto ha hab).eventually
    (isOpen_Ioo.mem_nhds (show b-a ∈ Set.Ioo ((b-a)/2) (2*(b-a)) by constructor <;> linarith))
  refine ⟨l, u, by dsimp [l]; positivity, by dsimp [u]; positivity, ?_⟩
  filter_upwards [hcounts, eventually_gt_atTop (1 : ℝ)] with T hcnt hT
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := (Real.log_pos hT).le
  obtain ⟨hlo, hhi⟩ := reciprocalMass_bounds ha0 hab hT0
  have hlo' := mul_le_mul_of_nonneg_left hlo hlog
  have hhi' := mul_le_mul_of_nonneg_left hhi hlog
  have heq (v : ℝ) : Real.log T * (((primeWindow a b T).card : ℝ) / (v * T)) =
      (Real.log T / T * ((primeWindow a b T).card : ℝ)) / v := by ring
  rw [heq] at hlo' hhi'
  constructor
  · have hc := div_le_div_of_nonneg_right hcnt.1.le hb0.le
    dsimp [l]
    calc
      _ = ((b-a)/2)/b := by ring
      _ ≤ _ := hc.trans hlo'
  · have hc := div_le_div_of_nonneg_right hcnt.2.le ha0.le
    exact hhi'.trans hc

def selectedPrimes (a b c d T : ℝ) : Finset ℕ := primeWindow a b T ∪ primeWindow c d T

/-- The full, unrestricted cofactor response at the selected prime. -/
def idealCoefficient (T : ℝ) (p : ℕ) : ℂ :=
  ((1 / (p : ℝ) : ℝ) : ℂ) * exponentialDensity ((p : ℝ) / T)

def idealCapacity (a b c d T : ℝ) : ℝ :=
  ∑ p ∈ selectedPrimes a b c d T, ‖idealCoefficient T p‖

def idealCenter (a b c d T : ℝ) : ℂ :=
  ∑ p ∈ selectedPrimes a b c d T, idealCoefficient T p

private theorem normalized_mem_primeWindow {a b T : ℝ} (hb : 0 < b) (hT : 0 < T)
    {p : ℕ} (hp : p ∈ primeWindow a b T) : (p : ℝ) / T ∈ Set.Icc a b := by
  obtain ⟨_, hlo, hhi⟩ := mem_primeWindow (mul_nonneg hb.le hT.le) hp
  exact ⟨((lt_div_iff₀ hT).mpr hlo).le, (div_le_iff₀ hT).mpr hhi⟩

private theorem primeWindow_disjoint {a b c d T : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hbc : b < c) (hT : 0 < T) : Disjoint (primeWindow a b T) (primeWindow c d T) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := normalized_mem_primeWindow hb hT hp
  have hq' := normalized_mem_primeWindow hd hT hq
  linarith [hp'.2, hq'.1]

private theorem norm_idealCoefficient (T : ℝ) (p : ℕ) :
    ‖idealCoefficient T p‖ = (1 / (p : ℝ)) * ‖exponentialDensity ((p : ℝ) / T)‖ := by
  rw [idealCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

private theorem phaseDefect_idealCoefficient (T : ℝ) (p q : ℕ) :
    phaseDefect (idealCoefficient T p) (idealCoefficient T q) =
      (1 / (p : ℝ)) * (1 / (q : ℝ)) *
        phaseDefect (exponentialDensity ((p : ℝ) / T)) (exponentialDensity ((q : ℝ) / T)) :=
  phaseDefect_real_mul _ _ (by positivity) (by positivity) _ _

private theorem idealCapacity_upper {a b c d T M : ℝ}
    (ha : 1 < a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hT : 0 < T)
    (hM : ∀ x : ℝ, 1 ≤ x → ‖exponentialDensity x‖ ≤ M) :
    idealCapacity a b c d T ≤ M * (reciprocalMass a b T + reciprocalMass c d T) := by
  have hb : 0 < b := by linarith
  have hd : 0 < d := by linarith
  have hdis := primeWindow_disjoint hb hd hbc hT (a := a)
  calc
    _ ≤ ∑ p ∈ selectedPrimes a b c d T, M * (1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hnorm : ‖exponentialDensity ((p : ℝ) / T)‖ ≤ M := by
        apply hM
        rcases Finset.mem_union.mp hp with hp | hp
        · have h := (normalized_mem_primeWindow hb hT hp).1
          linarith
        · have h := (normalized_mem_primeWindow hd hT hp).1
          linarith
      rw [norm_idealCoefficient, mul_comm M]
      exact mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by rw [← Finset.mul_sum, selectedPrimes, Finset.sum_union hdis]; rfl

private theorem idealCapacity_squared_gap {a b c d T δ : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hT : 0 < T)
    (hgap : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d,
      δ ≤ phaseDefect (exponentialDensity x) (exponentialDensity y)) :
    δ * reciprocalMass a b T * reciprocalMass c d T ≤
      (idealCapacity a b c d T) ^ 2 - ‖idealCenter a b c d T‖ ^ 2 := by
  have hP : primeWindow a b T ⊆ selectedPrimes a b c d T := Finset.subset_union_left
  have hQ : primeWindow c d T ⊆ selectedPrimes a b c d T := Finset.subset_union_right
  calc
    _ = ∑ p ∈ primeWindow a b T, ∑ q ∈ primeWindow c d T,
        δ * (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, reciprocalMass]
    _ ≤ ∑ p ∈ primeWindow a b T, ∑ q ∈ primeWindow c d T,
        phaseDefect (idealCoefficient T p) (idealCoefficient T q) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have h := hgap _ (normalized_mem_primeWindow hb hT hp)
        _ (normalized_mem_primeWindow hd hT hq)
      rw [phaseDefect_idealCoefficient]
      calc
        _ = ((1 / (p : ℝ)) * (1 / (q : ℝ))) * δ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ ∑ p ∈ selectedPrimes a b c d T, ∑ q ∈ primeWindow c d T,
        phaseDefect (idealCoefficient T p) (idealCoefficient T q) :=
      Finset.sum_le_sum_of_subset_of_nonneg hP fun p _ _ =>
        Finset.sum_nonneg fun q _ => phaseDefect_nonneg _ _
    _ ≤ ∑ p ∈ selectedPrimes a b c d T, ∑ q ∈ selectedPrimes a b c d T,
        phaseDefect (idealCoefficient T p) (idealCoefficient T q) :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum_of_subset_of_nonneg hQ
        fun q _ _ => phaseDefect_nonneg _ _
    _ = _ := (phaseDefect_sum _ _).symm

private theorem idealCapacity_log_gap {a b c d T δ M l₁ l₂ u₁ u₂ : ℝ}
    (ha : 1 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hδ : 0 < δ) (hM : 0 < M) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) (hT : 1 < T)
    (hFb : ∀ x : ℝ, 1 ≤ x → ‖exponentialDensity x‖ ≤ M)
    (hgap : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d,
      δ ≤ phaseDefect (exponentialDensity x) (exponentialDensity y))
    (h₁ : l₁ ≤ Real.log T * reciprocalMass a b T ∧
      Real.log T * reciprocalMass a b T ≤ u₁)
    (h₂ : l₂ ≤ Real.log T * reciprocalMass c d T ∧
      Real.log T * reciprocalMass c d T ≤ u₂) :
    δ * l₁ * l₂ / (2 * M * (u₁ + u₂)) ≤
      Real.log T * (idealCapacity a b c d T - ‖idealCenter a b c d T‖) := by
  let L := Real.log T
  let S := idealCapacity a b c d T
  let Z := ‖idealCenter a b c d T‖
  have hT0 : 0 < T := by linarith
  have hL : 0 ≤ L := (Real.log_pos hT).le
  have htriangle : Z ≤ S := norm_sum_le _ _
  have htriangle' : L * Z ≤ L * S := mul_le_mul_of_nonneg_left htriangle hL
  have hupper : L * S ≤ M * (u₁ + u₂) := by
    calc
      _ ≤ L * (M * (reciprocalMass a b T + reciprocalMass c d T)) :=
        mul_le_mul_of_nonneg_left (idealCapacity_upper ha hab hbc hcd hT0 hFb) hL
      _ = M * (L * reciprocalMass a b T + L * reciprocalMass c d T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h₁.2 h₂.2) hM.le
  have hsum : L * S + L * Z ≤ 2 * M * (u₁ + u₂) := by linarith
  have hmass₁ : 0 ≤ L * reciprocalMass a b T := hl₁.le.trans h₁.1
  have hprod := mul_le_mul h₁.1 h₂.1 hl₂.le hmass₁
  have hcross := idealCapacity_squared_gap (by linarith : 0 < b)
    (by linarith : 0 < d) hT0 hgap
  have hmain : δ * l₁ * l₂ ≤ (L * (S - Z)) * (L * S + L * Z) := by
    calc
      _ = δ * (l₁ * l₂) := by ring
      _ ≤ δ * ((L * reciprocalMass a b T) * (L * reciprocalMass c d T)) :=
        mul_le_mul_of_nonneg_left hprod hδ.le
      _ = L ^ 2 * (δ * reciprocalMass a b T * reciprocalMass c d T) := by ring
      _ ≤ L ^ 2 * (S ^ 2 - Z ^ 2) := mul_le_mul_of_nonneg_left hcross (sq_nonneg L)
      _ = _ := by ring
  apply (div_le_iff₀ (by positivity : 0 < 2 * M * (u₁ + u₂))).mpr
  exact hmain.trans (mul_le_mul_of_nonneg_left hsum
    (mul_nonneg hL (sub_nonneg.mpr htriangle)))

/-- The actual full density has a uniform prime-phase capacity surplus on two fixed intervals. -/
theorem exists_prime_phase_capacity_gap :
    ∃ a b c d κ : ℝ, 1 < a ∧ a < b ∧ b < c ∧ c < d ∧ 0 < κ ∧
      ∀ᶠ T : ℝ in atTop, κ ≤ Real.log T *
        (idealCapacity a b c d T - ‖idealCenter a b c d T‖) := by
  obtain ⟨a, b, c, d, δ, ha, hab, hbc, hcd, hδ, hgap⟩ := exists_phaseDefect_intervals
  obtain ⟨M, hM, hFb⟩ := density_bounded_above_one
  obtain ⟨l₁, u₁, hl₁, hu₁, h₁⟩ := eventual_reciprocalMass_bounds ha hab
  obtain ⟨l₂, u₂, hl₂, hu₂, h₂⟩ := eventual_reciprocalMass_bounds (by linarith : 1 < c) hcd
  refine ⟨a, b, c, d, δ*l₁*l₂/(2*M*(u₁+u₂)), ha, hab, hbc, hcd, by positivity, ?_⟩
  filter_upwards [h₁, h₂, eventually_gt_atTop (1 : ℝ)] with T h₁T h₂T hT
  exact idealCapacity_log_gap ha hab hbc hcd hδ hM hl₁ hl₂ hu₁ hu₂ hT hFb hgap h₁T h₂T

end
end RHTower.LiouvilleTwistedDensity
