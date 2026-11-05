import GaloisForLFunctions.FiniteFreeProbability.EulerProductDriftIsForced
import GaloisForLFunctions.HTGeometry.RealTaylorCoefficients
import GaloisForLFunctions.HTGeometry.LaguerrePolyaJensenConverse

/-!
# The real-zero horizon of symmetrized finite Euler products

For a finite set `S` of primes, `σ > 0` and a phase `c`, the symmetrized carrier

`C(z) = e^{icz} Π_{p∈S}(1 − p^{−σ} e^{−iz log p}) + (its reflection)
      = Σ_{T ⊆ S} w_T · 2 cos((c − λ_T) z)`

(`w_T = (−1)^{|T|} Π_T p^{−σ}`, `λ_T = Σ_T log p`) is a real even trigonometric sum.

**Theorem.** For `|S|` odd, `C` has only real zeros exactly when `c ≥ θ_S/2 = ½ Σ_{p∈S} log p`.

* `c ≥ θ_S/2`: the reversed Jensen polynomials of the unsymmetrized product are Hermite–Biehler
  stable (Walsh against the normalized Euler factors, then a downward translation), so every
  Jensen polynomial of `C` is real-rooted (Hermite–Biehler) and `C` is Laguerre–Pólya.
* `c < θ_S/2`: on the imaginary axis `C(iy) = 2 Σ_T w_T cosh((c − λ_T) y)` is positive at `y = 0`
  and dominated at large `y` by the term of `T = S`, of weight `−Π_S p^{−σ}`; it vanishes at some
  `y > 0`.

So the horizon of the finite free Hermite–Biehler route is exactly half the total log-frequency:
the finite free form of the carrier horizon `t = 2π e^{θ_S}`.
-/

open Polynomial Filter Topology Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace FiniteFreeProbability

noncomputable section

/-! ## Translations of reversed Jensen polynomials -/

/-- `e^{aD}` on polynomials of degree `≤ d` is the translation `p ↦ p(X + a)`. -/
theorem diffOp_trunc_expSeries {d : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ d) (a : ℂ) :
    diffOp (PowerSeries.trunc (d + 1) (expSeries a)) p = p.comp (X + C a) := by
  apply Polynomial.funext
  intro w
  rw [diffOp_eq_sum _ _ (n := d + 1) (PowerSeries.natDegree_trunc_lt _ _), eval_finsetSum, eval_comp, eval_add, eval_X, eval_C, add_comm w,
    ← taylor_eval, eval_eq_sum_range' (n := d + 1) (by rw [natDegree_taylor]; omega)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [eval_mul, eval_C, eval_iterate_derivative_eq, PowerSeries.coeff_trunc,
    if_pos (Finset.mem_range.1 hk), expSeries, PowerSeries.coeff_mk]
  have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

theorem jensenRev_expSeries_mul (d : ℕ) (a : ℂ) (G : PowerSeries ℂ) :
    jensenRev d (expSeries a * G) = (jensenRev d G).comp (X + C a) := by
  rw [jensenRev_mul, ffConv_comm (natDegree_jensenRev_le _ _) (natDegree_jensenRev_le _ _),
    expSeries, ffConv_jensenRev_right (natDegree_jensenRev_le _ _), ← expSeries,
    diffOp_trunc_expSeries (natDegree_jensenRev_le _ _)]

/-! ## Stability above the threshold -/

theorem eulerFactor_eq_expSeries_mul (q ℓ : ℂ) :
    eulerFactor q (ℓ / 2) = expSeries (ℓ / 2) * (1 - PowerSeries.C q * expSeries (-ℓ)) := by
  rw [eulerFactor, mul_sub, mul_one, mul_left_comm, expSeries_add]
  congr 3; ring

theorem translatedMobiusProduct_eq_expSeries_mul (S : Finset Nat.Primes) (σ c : ℝ) :
    translatedMobiusProduct S σ c = expSeries (I * (c - logFrequency S / 2)) *
      eulerProduct S (fun p => ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)) fun p => Real.log ((p : ℕ) : ℝ) := by
  rw [eulerProduct]
  have hfac : ∀ p ∈ S, eulerFactor ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)
      (I * ((Real.log ((p : ℕ) : ℝ) / 2 : ℝ) : ℂ)) =
      expSeries (I * Real.log ((p : ℕ) : ℝ) / 2) *
        (1 - PowerSeries.C ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
          expSeries (-(I * Real.log ((p : ℕ) : ℝ)))) := fun p _ => by
    rw [show I * ((Real.log ((p : ℕ) : ℝ) / 2 : ℝ) : ℂ) = (I * Real.log ((p : ℕ) : ℝ)) / 2 by
      push_cast; ring, eulerFactor_eq_expSeries_mul]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, prod_expSeries, ← mul_assoc,
    expSeries_add, translatedMobiusProduct, logFrequency]
  congr 2
  have hθ : ∑ p ∈ S, I * ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) / 2 =
      I * ((∑ p ∈ S, Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) / 2 := by
    rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_div]
  rw [hθ]; ring

/-- **Above the threshold all roots lie in the open lower half-plane.** -/
theorem im_neg_of_isRoot_jensenRev_translatedMobiusProduct {S : Finset Nat.Primes}
    (hS : S.Nonempty) {σ : ℝ} (hσ : 0 < σ) {c : ℝ} (hc : logFrequency S / 2 ≤ c) {d : ℕ}
    (hd : 1 ≤ d) {x : ℂ} (hx : (jensenRev d (translatedMobiusProduct S σ c)).IsRoot x) :
    x.im < 0 := by
  classical
  rw [translatedMobiusProduct_eq_expSeries_mul, jensenRev_expSeries_mul] at hx
  have hroot : (jensenRev d (eulerProduct S (fun p => ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ))
      fun p => Real.log ((p : ℕ) : ℝ))).IsRoot (x + I * (c - logFrequency S / 2)) := by
    simpa [IsRoot, eval_comp] using hx
  have h := (roots_jensenRev_eulerProduct _ _ hd S (fun p _ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos
        (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith))
    (fun p _ => Real.log_pos (by exact_mod_cast p.prop.one_lt))).2 hS _ hroot
  simp only [add_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add] at h
  have : ((c : ℂ) - (logFrequency S : ℂ) / 2).re = c - logFrequency S / 2 := by simp
  rw [this] at h
  linarith

/-! ## The symmetrized carrier as an entire function -/

/-- The symmetrized carrier `C(z) = Σ_T w_T (e^{i(c−λ_T)z} + e^{−i(c−λ_T)z})`. -/
def symEuler (S : Finset Nat.Primes) (σ c : ℝ) (z : ℂ) : ℂ :=
  ∑ T ∈ S.powerset, (mobiusWeight σ T : ℂ) *
    (Complex.exp (I * ((c - logFrequency T : ℝ) : ℂ) * z) +
      Complex.exp (-(I * ((c - logFrequency T : ℝ) : ℂ)) * z))

theorem differentiable_symEuler (S : Finset Nat.Primes) (σ c : ℝ) :
    Differentiable ℂ (symEuler S σ c) := by
  unfold symEuler; fun_prop

theorem symEuler_conj (S : Finset Nat.Primes) (σ c : ℝ) (z : ℂ) :
    symEuler S σ c (conj z) = conj (symEuler S σ c z) := by
  simp only [symEuler, map_sum, map_mul, map_add, Complex.conj_ofReal, ← Complex.exp_conj,
    map_neg, Complex.conj_I]
  refine Finset.sum_congr rfl fun T _ => ?_
  ring_nf

theorem iteratedDeriv_symEuler_zero (S : Finset Nat.Primes) (σ c : ℝ) (k : ℕ) :
    iteratedDeriv k (symEuler S σ c) 0 = ∑ T ∈ S.powerset, (mobiusWeight σ T : ℂ) *
      ((I * ((c - logFrequency T : ℝ) : ℂ)) ^ k + (-(I * ((c - logFrequency T : ℝ) : ℂ))) ^ k) := by
  unfold symEuler
  rw [iteratedDeriv_fun_sum fun T _ => by fun_prop]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [iteratedDeriv_const_mul_field]
  rw [show (fun z : ℂ => Complex.exp (I * ((c - logFrequency T : ℝ) : ℂ) * z) +
      Complex.exp (-(I * ((c - logFrequency T : ℝ) : ℂ)) * z)) =
      (fun z : ℂ => Complex.exp (I * ((c - logFrequency T : ℝ) : ℂ) * z)) +
      (fun z : ℂ => Complex.exp (-(I * ((c - logFrequency T : ℝ) : ℂ)) * z)) from rfl,
    iteratedDeriv_add (by fun_prop) (by fun_prop), iteratedDeriv_cexp_const_mul,
    iteratedDeriv_cexp_const_mul]
  simp

/-- The real Taylor coefficients of the carrier are those of the symmetrized power series. -/
theorem ofReal_realTaylorCoeff_symEuler (S : Finset Nat.Primes) (σ c : ℝ) (k : ℕ) :
    ((realTaylorCoeff (symEuler S σ c) k : ℝ) : ℂ) =
      PowerSeries.coeff k (translatedMobiusProduct S σ c) +
        conj (PowerSeries.coeff k (translatedMobiusProduct S σ c)) := by
  rw [ofReal_realTaylorCoeff (symEuler_conj S σ c), iteratedDeriv_symEuler_zero,
    translatedMobiusProduct_eq, map_sum, map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [PowerSeries.coeff_C_mul, expSeries, PowerSeries.coeff_mk]
  simp only [map_mul, map_div₀, map_pow, Complex.conj_ofReal, map_sub, Complex.conj_I,
    map_natCast]
  push_cast
  ring

/-- **Below the threshold: a purely imaginary zero.** -/
theorem exists_imaginary_zero_symEuler {S : Finset Nat.Primes} (hodd : Odd S.card) {σ : ℝ}
    (hσ : 0 < σ) {c : ℝ} (hc : c < logFrequency S / 2) :
    ∃ y : ℝ, 0 < y ∧ symEuler S σ c (I * y) = 0 := by
  classical
  have hS : S.Nonempty := Finset.card_pos.1 hodd.pos
  set g : ℝ → ℝ := fun y => ∑ T ∈ S.powerset,
    mobiusWeight σ T * (2 * Real.cosh ((c - logFrequency T) * y))
  have hval : ∀ y : ℝ, symEuler S σ c (I * y) = (g y : ℂ) := by
    intro y
    simp only [symEuler, g]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_cosh, Complex.cosh]
    have e1 : I * ((c - logFrequency T : ℝ) : ℂ) * (I * y) =
        -(((c - logFrequency T) * y : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    have e2 : -(I * ((c - logFrequency T : ℝ) : ℂ)) * (I * y) =
        (((c - logFrequency T) * y : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [e1, e2]; push_cast; ring
  -- the weights
  have hlogpos : ∀ p : Nat.Primes, 0 < Real.log ((p : ℕ) : ℝ) := fun p =>
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hqpos : ∀ p : Nat.Primes, 0 < ((p : ℕ) : ℝ) ^ (-σ) := fun p =>
    Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have hqlt : ∀ p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) < 1 := fun p =>
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
  have hsum0 : ∑ T ∈ S.powerset, mobiusWeight σ T = ∏ p ∈ S, (1 - ((p : ℕ) : ℝ) ^ (-σ)) := by
    rw [show (fun p : Nat.Primes => 1 - ((p : ℕ) : ℝ) ^ (-σ)) =
      fun p : Nat.Primes => (-((p : ℕ) : ℝ) ^ (-σ)) + 1 from funext fun p => by ring,
      Finset.prod_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_neg, mobiusWeight]
  have hg0 : 0 < g 0 := by
    simp only [g, mul_zero, Real.cosh_zero, mul_one]
    rw [← Finset.sum_mul, hsum0]
    exact mul_pos (Finset.prod_pos fun p _ => by linarith [hqlt p]) two_pos
  -- the dominant term at large `y`
  have hΘ : 0 < logFrequency S := Finset.sum_pos (fun p _ => hlogpos p) hS
  set a := Real.exp (logFrequency S - c)
  have hwS : mobiusWeight σ S = -∏ p ∈ S, ((p : ℕ) : ℝ) ^ (-σ) := by
    rw [mobiusWeight, hodd.neg_one_pow]; ring
  have hprodpos : 0 < ∏ p ∈ S, ((p : ℕ) : ℝ) ^ (-σ) := Finset.prod_pos fun p _ => hqpos p
  have hdom := eventually_sum_lt_pow (S.powerset.erase S) (fun T => 2 * mobiusWeight σ T)
    (fun T => Real.exp (abs (c - logFrequency T))) hprodpos (Real.exp_pos (logFrequency S - c))
    (fun T hT => by
      rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_exp]
      rcases Finset.mem_erase.1 hT with ⟨hTS, hTmem⟩
      rw [Finset.mem_powerset] at hTmem
      have hlo : 0 ≤ logFrequency T := Finset.sum_nonneg fun p _ => (hlogpos p).le
      have hhi : logFrequency T < logFrequency S := by
        obtain ⟨p, hpS, hpT⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2
          ⟨hTmem, hTS⟩)
        have := Finset.sum_lt_sum_of_subset hTmem hpS hpT (hlogpos p) (fun q _ _ => (hlogpos q).le)
        simpa [logFrequency] using this
      rw [abs_lt]; constructor <;> linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hdom
  set n := max N 1
  have hn := hN n (le_max_left _ _)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le one_pos (le_max_right N 1))
  have hgn : g n < 0 := by
    simp only [g]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self S), hwS]
    have hcosh_ge : Real.exp ((logFrequency S - c) * n) / 2 ≤
        Real.cosh ((c - logFrequency S) * n) := by
      rw [show (c - logFrequency S) * n = -((logFrequency S - c) * n) by ring, Real.cosh_neg,
        Real.cosh_eq]
      linarith [Real.exp_pos (-((logFrequency S - c) * n))]
    have hrest : ∑ T ∈ S.powerset.erase S,
        mobiusWeight σ T * (2 * Real.cosh ((c - logFrequency T) * n)) ≤
        ∑ T ∈ S.powerset.erase S, |2 * mobiusWeight σ T| *
          |Real.exp (abs (c - logFrequency T))| ^ n := by
      refine Finset.sum_le_sum fun T _ => ?_
      rw [abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul, abs_mul, abs_two]
      have hcosh : Real.cosh ((c - logFrequency T) * n) ≤
          Real.exp (n * abs (c - logFrequency T)) := by
        have habs : |(c - logFrequency T) * n| = n * |c - logFrequency T| := by
          rw [abs_mul, abs_of_pos hnpos]; ring
        rw [Real.cosh_eq, ← habs]
        have h1 := Real.exp_le_exp.2 (le_abs_self ((c - logFrequency T) * n))
        have h2 := Real.exp_le_exp.2 (neg_le_abs ((c - logFrequency T) * n))
        linarith
      calc mobiusWeight σ T * (2 * Real.cosh ((c - logFrequency T) * n)) ≤
            |mobiusWeight σ T| * (2 * Real.cosh ((c - logFrequency T) * n)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |mobiusWeight σ T| * (2 * Real.exp (n * abs (c - logFrequency T))) := by gcongr
        _ = _ := by ring
    have hpow : Real.exp ((logFrequency S - c) * n) = a ^ n := by
      rw [← Real.exp_nat_mul]; ring_nf
    have hmul := mul_le_mul_of_nonneg_left hcosh_ge hprodpos.le
    rw [hpow] at hmul
    linarith
  obtain ⟨y, hy, hgy⟩ := intermediate_value_Ioo' (le_of_lt hnpos)
    (show Continuous g by simp only [g]; fun_prop).continuousOn ⟨hgn, hg0⟩
  exact ⟨y, hy.1, by rw [hval, hgy]; simp⟩

/-! ## Real zeros above the threshold, and the horizon law -/

theorem constantCoeff_translatedMobiusProduct (S : Finset Nat.Primes) (σ c : ℝ) :
    PowerSeries.constantCoeff (translatedMobiusProduct S σ c) =
      ∏ p ∈ S, (1 - ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)) := by
  rw [translatedMobiusProduct, map_mul, constantCoeff_expSeries, one_mul, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, map_one, map_mul, PowerSeries.constantCoeff_C, constantCoeff_expSeries, mul_one]

/-- **Above the threshold every Jensen polynomial of the carrier is real-rooted.** -/
theorem splits_jensenPoly_symEuler {S : Finset Nat.Primes} (hS : S.Nonempty) {σ : ℝ}
    (hσ : 0 < σ) {c : ℝ} (hc : logFrequency S / 2 ≤ c) (d : ℕ) :
    (jensenPoly (realTaylorCoeff (symEuler S σ c)) d).Splits := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Polynomial.Splits.of_natDegree_le_one (by
      simp [jensenPoly])
  have hqlt : ∀ p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) < 1 := fun p =>
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
  have hcc : PowerSeries.constantCoeff (translatedMobiusProduct S σ c) ≠ 0 := by
    rw [constantCoeff_translatedMobiusProduct]
    refine Finset.prod_ne_zero_iff.2 fun p _ => ?_
    rw [sub_ne_zero]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [hqlt p]
  have hRP : (jensenReverse (realTaylorCoeff (symEuler S σ c)) d).map (algebraMap ℝ ℂ) =
      jensenRev d (translatedMobiusProduct S σ c) +
        conjPoly (jensenRev d (translatedMobiusProduct S σ c)) := by
    rw [← jensenRev_mk_eq_jensenReverse, jensenRev_eq_sum, jensenRev_eq_sum,
      Polynomial.map_sum, conjPoly, Polynomial.map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      PowerSeries.coeff_mk]
    rw [← add_mul, ← C_add]
    congr 2
    rw [Complex.coe_algebraMap, Complex.ofReal_mul, ofReal_realTaylorCoeff_symEuler]
    simp only [map_mul, map_natCast]
    push_cast
    ring
  have hreal : ∀ z : ℂ,
      (aeval z (jensenReverse (realTaylorCoeff (symEuler S σ c)) d) : ℂ) = 0 → z.im = 0 := by
    intro z hz
    have hz' : (jensenRev d (translatedMobiusProduct S σ c) +
        conjPoly (jensenRev d (translatedMobiusProduct S σ c))).IsRoot z := by
      rw [← hRP, IsRoot, ← eval₂_eq_eval_map, ← aeval_def]; exact hz
    exact im_eq_zero_of_isRoot_add_conjPoly (jensenRev_ne_zero hcc)
      (by rw [natDegree_jensenRev hcc]; exact hd)
      (fun r hr => im_neg_of_isRoot_jensenRev_translatedMobiusProduct hS hσ hc hd hr) hz'
  have hRs : (jensenReverse (realTaylorCoeff (symEuler S σ c)) d).Splits :=
    splits_of_forall_complex_root_real d _ (natDegree_jensenReverse_le _ _) hreal
  rw [← reflect_jensenReverse]
  exact Splits.reflect hRs (natDegree_jensenReverse_le _ _)

theorem symEuler_zero_ne {S : Finset Nat.Primes} {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    symEuler S σ c 0 ≠ 0 := by
  classical
  have hval : symEuler S σ c 0 = ((2 * ∏ p ∈ S, (1 - ((p : ℕ) : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
    simp only [symEuler, mul_zero, Complex.exp_zero]
    rw [show (fun p : Nat.Primes => 1 - ((p : ℕ) : ℝ) ^ (-σ)) =
      fun p : Nat.Primes => (-((p : ℕ) : ℝ) ^ (-σ)) + 1 from funext fun p => by ring,
      Finset.prod_add, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_neg, mobiusWeight]
    push_cast; ring
  rw [hval, Complex.ofReal_ne_zero]
  refine mul_ne_zero two_ne_zero (Finset.prod_ne_zero_iff.2 fun p _ => ?_)
  have := Real.rpow_lt_one_of_one_lt_of_neg (x := ((p : ℕ) : ℝ)) (z := -σ)
    (by exact_mod_cast p.prop.one_lt) (by linarith)
  linarith

/-- **Above the threshold the carrier is Laguerre–Pólya and all its zeros are real.** -/
theorem im_eq_zero_of_symEuler_eq_zero {S : Finset Nat.Primes} (hS : S.Nonempty) {σ : ℝ}
    (hσ : 0 < σ) {c : ℝ} (hc : logFrequency S / 2 ≤ c) {z : ℂ} (hz : symEuler S σ c z = 0) :
    z.im = 0 := by
  have hLP : LaguerrePolya (symEuler S σ c) :=
    laguerrePolya_of_splits_jensenPoly
      (fun w => hasSum_realTaylorCoeff (differentiable_symEuler S σ c) (symEuler_conj S σ c) w)
      (splits_jensenPoly_symEuler hS hσ hc)
  exact im_eq_zero_of_laguerrePolya hLP (symEuler_zero_ne hσ c) hz

/-- **The real-zero horizon of a symmetrized finite Euler product.** For an odd number of primes
and `σ > 0`, the carrier `Σ_T w_T 2cos((c − λ_T)z)` has only real zeros exactly when
`c ≥ ½ Σ_{p∈S} log p`. -/
theorem symEuler_realZeros_iff {S : Finset Nat.Primes} (hodd : Odd S.card) {σ : ℝ} (hσ : 0 < σ)
    (c : ℝ) : (∀ z, symEuler S σ c z = 0 → z.im = 0) ↔ logFrequency S / 2 ≤ c := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy, hzero⟩ := exists_imaginary_zero_symEuler hodd hσ hlt
    have := h _ hzero
    simp at this
    linarith
  · exact fun hc z hz => im_eq_zero_of_symEuler_eq_zero (Finset.card_pos.1 hodd.pos) hσ hc hz

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.symEuler_realZeros_iff
