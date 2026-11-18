import GaloisForLFunctions.CountingHolography.Sections.LocalCongruencesOfMidpointInjections
import GaloisForLFunctions.CountingHolography.Sections.CongruencesAfterClearingDenominators
import GaloisForLFunctions.RHTower.PrimeWindowSupply
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# The denominator of a midpoint section injection

The logarithm of the smallest scalar clearing congruences is comparable
to the length of the middle interval, uniformly over all injections.
This gives its exact double-logarithmic Tate coefficient.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology ArithmeticScatteringHolography

private theorem exists_clearing {n L s : ℕ} (f : Fin n × Fin n → Fin L × Fin s) :
    ∃ D : ℕ, 0 < D ∧ clearsSecond f D :=
  ⟨_,Nat.lcmUpto_pos _,lcmUpto_clearsSecond f⟩

/-- Smallest positive scalar clearing congruences of the narrow coordinate. -/
def leastClearing {n L s : ℕ} (f : Fin n × Fin n → Fin L × Fin s) : ℕ := by
  classical
  exact Nat.find (exists_clearing f)

theorem leastClearing_spec {n L s : ℕ} (f : Fin n × Fin n → Fin L × Fin s) :
    0 < leastClearing f ∧ clearsSecond f (leastClearing f) := by
  classical
  exact Nat.find_spec (exists_clearing f)

private theorem log_primorial (X : ℕ) : Real.log (primorial X) = Chebyshev.theta X := by
  rw [Chebyshev.theta_eq_log_primorial,Nat.floor_natCast]

/-- The prime mass between X and 2X, less the cost of one missed prime,
must be paid by every clearing denominator. -/
theorem theta_difference_le_log_clearing {n L s D X : ℕ} (e : (Fin n × Fin n) ↪ (Fin L × Fin s))
    (hL : L < n*n) (hD : clearsSecond e D) (hd : 0 < D)
    (hX : 0 < X) (hs : s ≤ X) (hn : 4*X ≤ n) :
    Chebyshev.theta (2*X : ℕ) - Chebyshev.theta X ≤ Real.log D + Real.log (2*X : ℕ) := by
  obtain ⟨q,hq,hqx,hdiv⟩ := primorial_dvd_cleared e hL hD hd hX hs hn
  have hp := primorial_pos X
  have hle := Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos hp hd) hq) hdiv
  have hlog := Real.log_le_log (Nat.cast_pos.mpr (primorial_pos (2*X))) (Nat.cast_le.mpr hle)
  rw [Nat.cast_mul,Nat.cast_mul,Real.log_mul (mul_ne_zero (Nat.cast_pos.mpr hp).ne'
    (Nat.cast_pos.mpr hd).ne') (Nat.cast_pos.mpr hq).ne',
    Real.log_mul (Nat.cast_pos.mpr hp).ne' (Nat.cast_pos.mpr hd).ne',log_primorial,log_primorial] at hlog
  linarith only [hlog,Real.log_le_log (Nat.cast_pos.mpr hq) (Nat.cast_le.mpr hqx)]

/-- On large boxes with a narrow side and insufficient wide side, the
least denominator has logarithm bounded above and below linearly in the
input side length. The upper bound works simultaneously for every map. -/
theorem eventually_log_leastClearing_bounds : ∀ᶠ n : ℕ in atTop,
    ∀ {L s : ℕ} (e : (Fin n × Fin n) ↪ (Fin L × Fin s)), L < n*n → 4*s ≤ n →
    (n : ℝ)/20 ≤ Real.log (leastClearing e) ∧ Real.log (leastClearing e) ≤ (Real.log 4+4)*n := by
  classical
  obtain ⟨X₀,hθ⟩ := _root_.RHTower.chebyshevTheta_remainder_eventually_le (by norm_num : (0 : ℝ) < 1/8)
  filter_upwards [eventually_ge_atTop (4*max 128 X₀)] with n hn
  intro L s e hL hs
  let X := n/4
  have hx : max 128 X₀ ≤ X := by dsimp only [X]; omega
  have hx₀ : X₀ ≤ X := (le_max_right _ _).trans hx
  have hx1 : 128 ≤ X := (le_max_left _ _).trans hx
  have hx' : (128 : ℝ) ≤ X := by exact_mod_cast hx1
  have hnx : n ≤ 4*X+3 := by dsimp only [X]; omega
  have hnx' : (n : ℝ) ≤ 4*(X : ℝ)+3 := by exact_mod_cast hnx
  have hD := leastClearing_spec e
  have hd := theta_difference_le_log_clearing e hL hD.2 hD.1 (show 0 < X by omega)
    (by dsimp only [X]; omega) (by dsimp only [X]; omega)
  have h₁ := (abs_le.mp (hθ X hx₀)).2
  have h₂ := (abs_le.mp (hθ (2*X) (by omega))).1
  have hlog : Real.log (2*(X : ℝ)) ≤ X/4 := by
    have he : (2*(X : ℝ)) = 16*(X/8) := by ring
    have hxpos : 0 < (X : ℝ)/8 := by linarith only [hx']
    rw [he, Real.log_mul (by norm_num) hxpos.ne']
    linarith only [Real.log_le_sub_one_of_pos hxpos,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 16),hx']
  push_cast at h₂ hd
  refine ⟨by linarith only [hnx',h₁,h₂,hlog,hd,hx'],?_⟩
  have hu : leastClearing e ≤ Nat.lcmUpto (n-1) :=
    Nat.find_min' (exists_clearing e) ⟨Nat.lcmUpto_pos _,lcmUpto_clearsSecond e⟩
  calc Real.log (leastClearing e) ≤ Real.log (Nat.lcmUpto (n-1)) :=
         Real.log_le_log (Nat.cast_pos.mpr hD.1) (Nat.cast_le.mpr hu)
    _ = Chebyshev.psi (n-1 : ℕ) := (Chebyshev.psi_eq_log_lcmUpto _).symm
    _ ≤ (Real.log 4+4)*(n-1 : ℕ) := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.sub_le n 1))
      (by linarith only [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)])

/-- Integer inputs to a bivariate polynomial in interval coordinates. -/
def boxPoint {n : ℕ} (x : Fin n × Fin n) : Bool → ℤ
  | false => x.1.val
  | true => x.2.val

/-- Scalar denominators in integer polynomial formulas clear the
congruences of the represented coordinate at every modulus. -/
theorem clearsSecond_of_polynomial {n L s D : ℕ} (f : Fin n × Fin n → Fin L × Fin s)
    (P : MvPolynomial Bool ℤ)
    (h : ∀ x, ((D*(f x).2.val : ℕ) : ℤ) = MvPolynomial.eval (boxPoint x) P) : clearsSecond f D := by
  intro v x y hx hy
  let φ := Int.castRingHom (ZMod v)
  have he : φ ∘ boxPoint x = φ ∘ boxPoint y := by
    funext i
    cases i
    · simpa [φ,boxPoint] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hx
    · simpa [φ,boxPoint] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hy
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hx' := congrArg φ (h x)
  have hy' := congrArg φ (h y)
  rw [MvPolynomial.map_eval,he] at hx'
  rw [MvPolynomial.map_eval] at hy'
  simpa [φ] using hx'.trans hy'.symm

/-- A polynomial presentation of the narrow output needs an exponentially
large denominator in the input side length. -/
theorem eventually_log_polynomial_denominator : ∀ᶠ n : ℕ in atTop,
    ∀ {L s D : ℕ} (e : (Fin n × Fin n) ↪ (Fin L × Fin s)) (P : MvPolynomial Bool ℤ),
      L < n*n → 4*s ≤ n → 0 < D →
      (∀ x, ((D*(e x).2.val : ℕ) : ℤ) = MvPolynomial.eval (boxPoint x) P) →
      (n : ℝ)/20 ≤ Real.log D := by
  classical
  filter_upwards [eventually_log_leastClearing_bounds] with n hn
  intro L s D e P hL hs hD h
  have he : leastClearing e ≤ D := Nat.find_min' (exists_clearing e) ⟨hD,clearsSecond_of_polynomial e P h⟩
  exact (hn e hL hs).1.trans (Real.log_le_log (Nat.cast_pos.mpr (leastClearing_spec e).1) (Nat.cast_le.mpr he))

/-- The logarithm of the logarithm of the least denominator has a uniform
quadratic limit over all actual section injections on a positive ray. -/
theorem eventually_loglog_sectionDenominator {N : ℕ} {b : Fin N → ℤ} (hb : 0 < integerProbe N b)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ m : ℕ in atTop, ∀ e : rayProductEmbedding b m,
    |Real.log (Real.log (leastClearing (ordinalEmbedding b m e))) / (m : ℝ)^2 -
      9*integerProbe N b| < ε := by
  let n := rayCard b 3
  have hr : Tendsto (fun m : ℕ => Real.log (n m)/(m : ℝ)^2) atTop (𝓝 (9*integerProbe N b)) := by
    convert rayCard_tateLimit hb 3 using 1
    norm_num
  have hnat : Tendsto n atTop atTop := by
    apply tendsto_atTop.mpr
    intro U
    have hC : Tendsto (fun m : ℕ => Real.log (U+1 : ℕ)/(m : ℝ)^2) atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
    filter_upwards [hC.eventually_lt_const (show 0 < 9*integerProbe N b/2 by positivity),
      hr.eventually_const_lt (show 9*integerProbe N b/2 < 9*integerProbe N b by linarith),
      eventually_ge_atTop 1] with m hc hm hm1
    have h := hc.trans hm
    rw [div_lt_div_iff_of_pos_right (by positivity : 0 < (m : ℝ)^2),
      Real.log_lt_log_iff (by positivity) (Nat.cast_pos.mpr (rayCard_pos b 3 m))] at h
    have ht : U+1 < n m := by exact_mod_cast h
    omega
  let c := Real.log 4+4
  have hc : 0 < c := by dsimp [c]; linarith only [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
  have hd (a : ℝ) : Tendsto (fun m : ℕ => a/(m : ℝ)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have hl := (hr.sub (hd (Real.log 20))).eventually_const_lt
    (show 9*integerProbe N b-ε < 9*integerProbe N b-0 by linarith)
  have hu := ((hd (Real.log c)).add hr).eventually_lt_const
    (show 0+9*integerProbe N b < 9*integerProbe N b+ε by linarith)
  filter_upwards [hnat.eventually eventually_log_leastClearing_bounds,eventually_wide_lt_square hb,
    eventually_narrow_mul_lt_middle hb 4 (by decide),hl,hu] with m hm hL hs hl' hu'
  intro e
  obtain ⟨h₁,h₂⟩ := hm (ordinalEmbedding b m e) hL hs.le
  have hn : 0 < (n m : ℝ) := Nat.cast_pos.mpr (rayCard_pos b 3 m)
  have hpos := (div_pos hn (by norm_num : (0:ℝ)<20)).trans_le h₁
  have hlo := Real.log_le_log (div_pos hn (by norm_num : (0:ℝ)<20)) h₁
  have hup := Real.log_le_log hpos h₂
  change _ ≤ Real.log (c*n m) at hup
  rw [Real.log_mul hc.ne' hn.ne'] at hup
  rw [Real.log_div hn.ne' (by norm_num)] at hlo
  have dlo := div_le_div_of_nonneg_right hlo (sq_nonneg (m : ℝ))
  have dup := div_le_div_of_nonneg_right hup (sq_nonneg (m : ℝ))
  rw [add_div] at dup
  rw [sub_div] at dlo
  rw [abs_lt]
  exact ⟨by linarith only [hl',dlo], by linarith only [hu',dup]⟩

#print axioms eventually_log_polynomial_denominator
#print axioms eventually_log_leastClearing_bounds
#print axioms eventually_loglog_sectionDenominator

end GaloisForLFunctions.CountingHolography.Sections
