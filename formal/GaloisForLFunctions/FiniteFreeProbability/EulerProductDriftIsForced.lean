import GaloisForLFunctions.FiniteFreeProbability.EulerNormalizationSharpness
import Mathlib.NumberTheory.PrimeCounting

/-!
# The Hermite–Biehler drift of a finite Euler product is forced

For a finite set `S` of primes and `σ > 0`, the Möbius-side Euler product
`Π_{p∈S} (1 − p^{−σ} e^{−iw log p}) = Σ_{T ⊆ S} (−1)^{|T|} (Π_T p^{−σ}) e^{−iw λ_T}`,
`λ_T = Σ_{p∈T} log p`, translated by `e^{icw}`, has reversed Jensen polynomials

`R_d = Σ_{T ⊆ S} w_T (X + ic − iλ_T)^d`.

On the imaginary axis `X = iy` this is `i^d Σ_T w_T (y + c − λ_T)^d`. The extreme frequencies
`0` and `θ_S = Σ_{p∈S} log p` carry weights `1` and `(−1)^{|S|} Π p^{−σ}`; for degrees with
`d + |S|` odd their contributions have opposite signs below the bisector `y + c = θ_S/2`. At the
bisector the weight-one term wins, slightly below it the other extreme wins, and all intermediate
frequencies are exponentially smaller. Hence for every `c < θ_S/2` and all large such `d` there is a
root `iy` with `y > 0`.

**Theorem.** The normalized products are stable at every degree exactly from the translation
`θ_S/2` on; below it stability fails at large degree. Since `θ_S` is unbounded, no bounded
translation stabilizes all finite Euler products, for every `σ > 0`, in particular in the region of
absolute convergence: the obstruction is the phase, not convergence.
-/

open Polynomial Filter Topology Complex Finset

namespace FiniteFreeProbability

noncomputable section

/-! ## Exponential domination -/

/-- Finitely many smaller exponentials are eventually dominated. -/
theorem eventually_sum_lt_pow {ι : Type*} (s : Finset ι) (B b : ι → ℝ) {A a : ℝ} (hA : 0 < A)
    (ha : 0 < a) (hb : ∀ i ∈ s, |b i| < a) :
    ∀ᶠ d : ℕ in atTop, ∑ i ∈ s, |B i| * |b i| ^ d < A * a ^ d := by
  have hlim : Tendsto (fun d : ℕ => ∑ i ∈ s, |B i| * (|b i| / a) ^ d) atTop (𝓝 0) := by
    have := tendsto_finsetSum s fun i hi => (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg (abs_nonneg _) ha.le) ((div_lt_one ha).2 (hb i hi))).const_mul |B i|
    simpa using this
  filter_upwards [hlim.eventually (gt_mem_nhds hA)] with d hd
  have hpos : 0 < a ^ d := pow_pos ha d
  have hrw : ∑ i ∈ s, |B i| * |b i| ^ d = a ^ d * ∑ i ∈ s, |B i| * (|b i| / a) ^ d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow]; field_simp
  rw [hrw, mul_comm A]
  exact mul_lt_mul_of_pos_left hd hpos

theorem abs_sum_le_sum_abs_pow {ι : Type*} (s : Finset ι) (B b : ι → ℝ) (d : ℕ) :
    |∑ i ∈ s, B i * b i ^ d| ≤ ∑ i ∈ s, |B i| * |b i| ^ d := by
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_mul, abs_pow]

/-! ## Signed exponential mixtures on the imaginary axis -/

/-- **A positive root on the axis.** A real mixture `Σ w_i (y + c − λ_i)^d` with the extreme
frequencies `0` (weight `w₀`) and `Θ` (weight `w₁ ≠ 0`, `|w₁| < w₀`) and all other frequencies
strictly inside `(0, Θ)` has a root `y > 0` for all large `d` with `(−1)^d w₁ < 0`, when
`c < Θ/2`. -/
theorem eventually_exists_pos_root_signedMixture {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w lam : ι → ℝ) {i₀ i₁ : ι} (hi₀ : i₀ ∈ s) (hi₁ : i₁ ∈ s) (h01 : i₀ ≠ i₁) {Θ c : ℝ}
    (hΘ : 0 < Θ) (hl₀ : lam i₀ = 0) (hl₁ : lam i₁ = Θ)
    (hmid : ∀ i ∈ s, i ≠ i₀ → i ≠ i₁ → 0 < lam i ∧ lam i < Θ) (hw₁ : w i₁ ≠ 0)
    (hw : |w i₁| < w i₀) (hc : c < Θ / 2) :
    ∀ᶠ d : ℕ in atTop, (-1) ^ d * w i₁ < 0 →
      ∃ y : ℝ, 0 < y ∧ ∑ i ∈ s, w i * (y + c - lam i) ^ d = 0 := by
  set m := Θ / 2
  have hm : 0 < m := by positivity
  set y₀ := m - c
  have hy₀ : 0 < y₀ := by simp only [y₀]; linarith
  set δ := y₀ / 2
  have hδ : 0 < δ := by positivity
  set t := (s.erase i₀).erase i₁
  have hsplit : ∀ f : ι → ℝ, ∑ i ∈ s, f i = f i₀ + f i₁ + ∑ i ∈ t, f i := by
    intro f
    rw [← Finset.add_sum_erase s f hi₀, ← Finset.add_sum_erase (s.erase i₀) f
      (Finset.mem_erase.2 ⟨h01.symm, hi₁⟩)]
    ring
  have hmem : ∀ i ∈ t, i ∈ s ∧ i ≠ i₀ ∧ i ≠ i₁ := fun i hi => by
    rcases Finset.mem_erase.1 hi with ⟨h1, hi'⟩
    rcases Finset.mem_erase.1 hi' with ⟨h0, hs⟩
    exact ⟨hs, h0, h1⟩
  -- positivity at the bisector
  have hpos := eventually_sum_lt_pow t w (fun i => m - lam i) (sub_pos.2 hw) hm (fun i hi => by
    obtain ⟨hs, h0, h1⟩ := hmem i hi
    obtain ⟨hlo, hhi⟩ := hmid i hs h0 h1
    rw [abs_lt]; constructor <;> simp only [m] <;> linarith)
  -- negativity just below it
  have hneg := eventually_sum_lt_pow (insert i₀ t) w
    (fun i => if i = i₀ then m - δ else m - δ - lam i) (abs_pos.2 hw₁) (by linarith : 0 < m + δ)
    (fun i hi => by
      rcases Finset.mem_insert.1 hi with h | hi
      · rw [if_pos h, abs_lt]; constructor <;> linarith
      · obtain ⟨hs, h0, h1⟩ := hmem i hi
        obtain ⟨hlo, hhi⟩ := hmid i hs h0 h1
        simp only [if_neg h0]; rw [abs_lt]; constructor <;> simp only [m] <;> linarith)
  filter_upwards [hpos, hneg] with d hdpos hdneg hsign
  have hsabs : (-1) ^ d * w i₁ = -|w i₁| := by
    have h1 : |(-1 : ℝ) ^ d * w i₁| = |w i₁| := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul]
    rw [← h1, abs_of_neg hsign, neg_neg]
  set g : ℝ → ℝ := fun y => ∑ i ∈ s, w i * (y + c - lam i) ^ d
  have hg0 : 0 < g y₀ := by
    simp only [g]
    rw [hsplit]
    have e0 : y₀ + c - lam i₀ = m := by simp only [y₀, hl₀]; ring
    have e1 : y₀ + c - lam i₁ = -m := by simp only [y₀, hl₁, m]; ring
    rw [e0, e1, neg_pow, ← mul_assoc, mul_comm (w i₁), hsabs]
    have hrest : ∀ i ∈ t, y₀ + c - lam i = m - lam i := fun i _ => by simp only [y₀]; ring
    rw [Finset.sum_congr rfl fun i hi => by rw [hrest i hi]]
    have := abs_sum_le_sum_abs_pow t w (fun i => m - lam i) d
    have := neg_abs_le (∑ i ∈ t, w i * (m - lam i) ^ d)
    nlinarith
  have hgB : g (y₀ - δ) < 0 := by
    simp only [g]
    rw [hsplit]
    have e0 : y₀ - δ + c - lam i₀ = m - δ := by simp only [y₀, hl₀]; ring
    have e1 : y₀ - δ + c - lam i₁ = -(m + δ) := by simp only [y₀, hl₁, m]; ring
    rw [e0, e1, neg_pow, ← mul_assoc, mul_comm (w i₁), hsabs]
    have hrest : ∀ i ∈ t, y₀ - δ + c - lam i = m - δ - lam i := fun i _ => by simp only [y₀]; ring
    rw [Finset.sum_congr rfl fun i hi => by rw [hrest i hi]]
    have hi₀t : i₀ ∉ t := fun h => (hmem i₀ h).2.1 rfl
    rw [Finset.sum_insert hi₀t, if_pos rfl] at hdneg
    have hcongr : ∑ i ∈ t, |w i| * |if i = i₀ then m - δ else m - δ - lam i| ^ d =
        ∑ i ∈ t, |w i| * |m - δ - lam i| ^ d :=
      Finset.sum_congr rfl fun i hi => by rw [if_neg (hmem i hi).2.1]
    rw [hcongr] at hdneg
    have h1 := abs_sum_le_sum_abs_pow t w (fun i => m - δ - lam i) d
    have h2 := le_abs_self (∑ i ∈ t, w i * (m - δ - lam i) ^ d)
    have h3 : w i₀ * (m - δ) ^ d ≤ |w i₀| * |m - δ| ^ d := by
      rw [← abs_pow, ← abs_mul]; exact le_abs_self _
    nlinarith
  have hcont : Continuous g := by
    simp only [g]; fun_prop
  obtain ⟨y, hy, hgy⟩ := intermediate_value_Ioo (by linarith : y₀ - δ ≤ y₀) hcont.continuousOn
    ⟨hgB, hg0⟩
  exact ⟨y, by simp only [δ] at hy; linarith [hy.1], hgy⟩

/-! ## Finite Möbius-side Euler products -/

theorem expSeries_add (a b : ℂ) : expSeries a * expSeries b = expSeries (a + b) := by
  have h : ∀ c : ℂ, expSeries c = PowerSeries.rescale c (PowerSeries.exp ℂ) := by
    intro c; ext n; simp [expSeries, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, div_eq_mul_inv]
  rw [h, h, h, PowerSeries.exp_mul_exp_eq_exp_add]

theorem expSeries_zero : expSeries (0 : ℂ) = 1 := by
  ext n; rcases n with _ | n <;> simp [expSeries, PowerSeries.coeff_one]

theorem prod_expSeries {ι : Type*} (T : Finset ι) (f : ι → ℂ) :
    ∏ i ∈ T, expSeries (f i) = expSeries (∑ i ∈ T, f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [expSeries_zero]
  | insert a T ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, expSeries_add]

theorem jensenRev_sum {ι : Type*} (d : ℕ) (T : Finset ι) (f : ι → PowerSeries ℂ) :
    jensenRev d (∑ i ∈ T, f i) = ∑ i ∈ T, jensenRev d (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp [jensenRev, diffOp]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [jensenRev, map_add, diffOp, LinearMap.add_apply]

/-- The Möbius weight `(−1)^{|T|} Π_T p^{−σ}` and frequency `Σ_T log p` of a set of primes. -/
def mobiusWeight (σ : ℝ) (T : Finset Nat.Primes) : ℝ :=
  (-1) ^ T.card * ∏ p ∈ T, ((p : ℕ) : ℝ) ^ (-σ)

def logFrequency (T : Finset Nat.Primes) : ℝ := ∑ p ∈ T, Real.log ((p : ℕ) : ℝ)

/-- The translated finite Möbius-side Euler product `e^{icw} Π_{p∈S} (1 − p^{−σ} e^{−iw log p})`. -/
def translatedMobiusProduct (S : Finset Nat.Primes) (σ c : ℝ) : PowerSeries ℂ :=
  expSeries (I * c) * ∏ p ∈ S, (1 - PowerSeries.C ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
    expSeries (-(I * Real.log ((p : ℕ) : ℝ))))

theorem translatedMobiusProduct_eq (S : Finset Nat.Primes) (σ c : ℝ) :
    translatedMobiusProduct S σ c = ∑ T ∈ S.powerset,
      PowerSeries.C ((mobiusWeight σ T : ℝ) : ℂ) * expSeries (I * c - I * logFrequency T) := by
  classical
  rw [translatedMobiusProduct]
  have hp : ∀ p ∈ S, (1 - PowerSeries.C ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
      expSeries (-(I * Real.log ((p : ℕ) : ℝ)))) =
      (-(PowerSeries.C ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
        expSeries (-(I * Real.log ((p : ℕ) : ℝ))))) + 1 := fun p _ => by ring
  rw [Finset.prod_congr rfl hp, Finset.prod_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_const_one, mul_one, Finset.prod_neg, Finset.prod_mul_distrib, prod_expSeries,
    ← map_prod, mobiusWeight, logFrequency]
  have hexp : expSeries (I * c) * expSeries (∑ p ∈ T, -(I * Real.log ((p : ℕ) : ℝ))) =
      expSeries (I * c - I * ∑ p ∈ T, Real.log ((p : ℕ) : ℝ)) := by
    rw [expSeries_add]; congr 1; push_cast; rw [Finset.sum_neg_distrib, Finset.mul_sum]; ring
  calc expSeries (I * c) * ((-1) ^ T.card * (PowerSeries.C (∏ p ∈ T, ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) :
        ℂ)) * expSeries (∑ p ∈ T, -(I * Real.log ((p : ℕ) : ℝ)))))
      = PowerSeries.C ((-1) ^ T.card * ∏ p ∈ T, ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)) *
          (expSeries (I * c) * expSeries (∑ p ∈ T, -(I * Real.log ((p : ℕ) : ℝ)))) := by
        rw [map_mul, map_pow, map_neg, map_one]; ring
    _ = _ := by rw [hexp]; push_cast; ring

/-- On the imaginary axis the reversed Jensen polynomial is a real signed mixture. -/
theorem eval_jensenRev_translatedMobiusProduct_I_mul (S : Finset Nat.Primes) (σ c y : ℝ) (d : ℕ) :
    (jensenRev d (translatedMobiusProduct S σ c)).eval (I * y) =
      I ^ d * ((∑ T ∈ S.powerset, mobiusWeight σ T * (y + c - logFrequency T) ^ d : ℝ) : ℂ) := by
  rw [translatedMobiusProduct_eq, jensenRev_sum, eval_finsetSum]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [jensenRev_C_mul, expSeries, jensenRev_exp]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X]
  rw [show I * (y : ℂ) + (I * c - I * logFrequency T) = I * ((y : ℂ) + c - logFrequency T) by ring,
    mul_pow]
  ring

/-- **The drift of a finite Euler product is forced.** For a nonempty set of primes, `σ > 0` and
`c < θ_S/2`, the translated product has a reversed Jensen root in the open upper half-plane for all
large degrees `d` with `d + |S|` odd. -/
theorem eventually_exists_upper_root_translatedMobiusProduct (S : Finset Nat.Primes)
    (hS : S.Nonempty) {σ : ℝ} (hσ : 0 < σ) {c : ℝ} (hc : c < logFrequency S / 2) :
    ∀ᶠ d : ℕ in atTop, Odd (d + S.card) →
      ∃ x : ℂ, (jensenRev d (translatedMobiusProduct S σ c)).IsRoot x ∧ 0 < x.im := by
  classical
  have hlogpos : ∀ p : Nat.Primes, 0 < Real.log ((p : ℕ) : ℝ) := fun p =>
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hqlt : ∀ p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) < 1 := fun p =>
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
  have hqpos : ∀ p : Nat.Primes, 0 < ((p : ℕ) : ℝ) ^ (-σ) := fun p =>
    Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have hΘ : 0 < logFrequency S := Finset.sum_pos (fun p _ => hlogpos p) hS
  have hprodpos : 0 < ∏ p ∈ S, ((p : ℕ) : ℝ) ^ (-σ) := Finset.prod_pos fun p _ => hqpos p
  have hprodlt : ∏ p ∈ S, ((p : ℕ) : ℝ) ^ (-σ) < 1 := by
    obtain ⟨p, hp⟩ := hS
    rw [← Finset.mul_prod_erase S _ hp]
    have hle : ∏ q ∈ S.erase p, ((q : ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Finset.prod_le_one (fun q _ => (hqpos q).le) (fun q _ => (hqlt q).le)
    calc ((p : ℕ) : ℝ) ^ (-σ) * ∏ q ∈ S.erase p, ((q : ℕ) : ℝ) ^ (-σ)
        ≤ ((p : ℕ) : ℝ) ^ (-σ) * 1 := mul_le_mul_of_nonneg_left hle (hqpos p).le
      _ < 1 := by rw [mul_one]; exact hqlt p
  have habs : |mobiusWeight σ S| = ∏ p ∈ S, ((p : ℕ) : ℝ) ^ (-σ) := by
    rw [mobiusWeight, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hprodpos]
  have hmix := eventually_exists_pos_root_signedMixture S.powerset (mobiusWeight σ) logFrequency
    (i₀ := ∅) (i₁ := S) (Finset.empty_mem_powerset S) (Finset.mem_powerset_self S)
    (fun h => hS.ne_empty h.symm) hΘ (by simp [logFrequency]) rfl
    (fun T hT h0 h1 => by
      rw [Finset.mem_powerset] at hT
      refine ⟨Finset.sum_pos (fun p _ => hlogpos p) (Finset.nonempty_iff_ne_empty.2 h0), ?_⟩
      have hss : T ⊂ S := Finset.ssubset_iff_subset_ne.2 ⟨hT, h1⟩
      obtain ⟨p, hpS, hpT⟩ := Finset.exists_of_ssubset hss
      have := Finset.sum_lt_sum_of_subset hT hpS hpT (hlogpos p) (fun q _ _ => (hlogpos q).le)
      simpa [logFrequency] using this)
    (fun h0 => by rw [← abs_eq_zero, habs] at h0; linarith)
    (by rw [habs, show mobiusWeight σ ∅ = 1 by simp [mobiusWeight]]; exact hprodlt)
    hc
  filter_upwards [hmix] with d hd hpar
  have hsign : (-1) ^ d * mobiusWeight σ S < 0 := by
    rw [mobiusWeight, ← mul_assoc, ← pow_add, hpar.neg_one_pow]
    linarith
  obtain ⟨y, hy, hroot⟩ := hd hsign
  refine ⟨I * y, ?_, by simpa using hy⟩
  rw [IsRoot, eval_jensenRev_translatedMobiusProduct_I_mul, hroot]
  simp

/-- Sets of primes with arbitrarily large total frequency. -/
theorem exists_primes_logFrequency_gt (B : ℝ) :
    ∃ S : Finset Nat.Primes, S.Nonempty ∧ B < logFrequency S := by
  classical
  set k := 2 * ⌈|B| / Real.log 2⌉₊ + 1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set f : ℕ → Nat.Primes := fun i => ⟨Nat.nth Nat.Prime i, Nat.prime_nth_prime i⟩
  have hf : Function.Injective f := fun i j h => by
    have := congrArg Subtype.val h
    exact Nat.nth_injective Nat.infinite_setOf_prime this
  refine ⟨(Finset.range k).image f, ?_, ?_⟩
  · exact (Finset.nonempty_range_iff.2 (by omega)).image f
  · have hge : ∀ p ∈ (Finset.range k).image f, Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) := fun p _ =>
      Real.log_le_log (by norm_num) (by exact_mod_cast p.prop.two_le)
    have hsum := Finset.card_nsmul_le_sum _ _ _ hge
    rw [Finset.card_image_of_injective _ hf, Finset.card_range, nsmul_eq_mul] at hsum
    have hk : |B| / Real.log 2 ≤ ⌈|B| / Real.log 2⌉₊ := Nat.le_ceil _
    have hk' : |B| ≤ ⌈|B| / Real.log 2⌉₊ * Real.log 2 := by
      rwa [div_le_iff₀ hl2] at hk
    have : B < (k : ℝ) * Real.log 2 := by
      simp only [k]; push_cast
      nlinarith [le_abs_self B]
    simp only [logFrequency]
    linarith

/-- **No bounded normalization stabilizes all finite Euler products.** For every `σ > 0` and every
translation `c`, some finite Euler product translated by `e^{icw}` has reversed Jensen roots in the
open upper half-plane at infinitely many degrees. -/
theorem no_uniform_translation_stabilizes_euler_products {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    ∃ S : Finset Nat.Primes, ∃ᶠ d : ℕ in atTop,
      ∃ x : ℂ, (jensenRev d (translatedMobiusProduct S σ c)).IsRoot x ∧ 0 < x.im := by
  obtain ⟨S, hne, hS⟩ := exists_primes_logFrequency_gt (2 * c)
  refine ⟨S, ?_⟩
  have hev := eventually_exists_upper_root_translatedMobiusProduct S hne hσ (by linarith : c < _)
  have hfreq : ∃ᶠ d : ℕ in atTop, Odd (d + S.card) := by
    refine Filter.frequently_atTop.2 fun N => ⟨2 * N + 1 + S.card, by omega, ?_⟩
    rw [Nat.odd_iff]; omega
  exact (hfreq.and_eventually hev).mono fun d ⟨hodd, h⟩ => h hodd

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eventually_exists_upper_root_translatedMobiusProduct
#print axioms FiniteFreeProbability.no_uniform_translation_stabilizes_euler_products
