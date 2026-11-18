import GaloisForLFunctions.CountingHolography.Sections.TheDyadicPrimeWeightOfSquareConductors
import GaloisForLFunctions.CountingHolography.Sections.ANegativePrimeWindowAtEveryMultiplicity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.PoleMomentsFromSeparatedGraphContacts

/-! # The first logarithmic moment of the square prime profile

The translate by log four cancels the zeroth half moment. Its first half
moment equals minus twice log four times the positive autocorrelation mass.
The same strictly negative quantity is a limit over ordinary primes.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology MeasureTheory ArithmeticCastelnuovoSeveri ArithmeticWeightTheory
open _root_.RHTower.WeilDeletion BiScaleUncertainty.ChebyshevGauge

private theorem autocorr_compact : HasCompactSupport splineAutoCorr := by
  rw [show splineAutoCorr = upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
  exact hasCompactSupport_upow 1 7

/-- Positive half moment of the cubic spline autocorrelation. -/
def squareAutocorrelationMass := ∫ u : ℝ, splineAutoCorr u*Real.exp (u/2)

theorem squareAutocorrelationMass_pos : 0 < squareAutocorrelationMass := by
  let F := fun u : ℝ => splineAutoCorr u*Real.exp (u/2)
  have hc : Continuous F := continuous_splineAutoCorr.mul (by fun_prop)
  have hk : HasCompactSupport F := autocorr_compact.mul_right
  have hn (u : ℝ) : 0 ≤ F u := mul_nonneg (splineAutoCorr_nonneg _) (Real.exp_pos _).le
  have hp : F 0 ≠ 0 := by simpa [F] using splineAutoCorr_zero_pos.ne'
  exact (integral_pos_iff_support_of_nonneg hn (hc.integrable_of_hasCompactSupport hk)).mpr
    (hc.isOpen_support.measure_pos volume ⟨0,hp⟩)

/-- The limiting signed prime measure is the difference of a positive
measure and its translate by log four. -/
theorem squareLogProfile_test_translation {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ u : ℝ, (g u*squareLogProfile u)*Real.exp (u/2)) =
      2*∫ u : ℝ, (g u-g (u+Real.log 4))*(splineAutoCorr u*Real.exp (u/2)) := by
  let b := Real.log 4
  let F := fun u : ℝ => splineAutoCorr u*Real.exp (u/2)
  let G := fun u : ℝ => g u*F u
  let Q := fun u : ℝ => g (u+b)*F u
  have hc : Continuous F := continuous_splineAutoCorr.mul (by fun_prop)
  have hk : HasCompactSupport F := autocorr_compact.mul_right
  have hG : Integrable G := (hg.mul hc).integrable_of_hasCompactSupport hk.mul_left
  have hQ : Integrable Q := ((hg.comp (continuous_id.add continuous_const)).mul hc).integrable_of_hasCompactSupport hk.mul_left
  have he : Real.exp (b/2)=2 := by
    have hl : b/2=Real.log 2 := by
      dsimp only [b]
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; ring
    rw [hl,Real.exp_log (by norm_num)]
  have hfun : (fun u : ℝ => (g u*squareLogProfile u)*Real.exp (u/2)) =
      fun u => 2*G u-2*Q (u-b) := by
    funext u
    have hs : Real.exp (u/2)=Real.exp ((u-b)/2)*2 := by
      rw [← he,← Real.exp_add]; congr 1; ring
    dsimp only [G,Q,F]
    rw [sub_add_cancel]
    change (g u*(2*splineAutoCorr u-splineAutoCorr (u-b)))*Real.exp (u/2)=_
    rw [hs]
    ring
  rw [hfun,integral_sub (hG.const_mul 2) ((hQ.comp_sub_right b).const_mul 2),
    integral_const_mul,integral_const_mul,integral_sub_right_eq_self Q b]
  have hdiff : (fun u : ℝ => (g u-g (u+b))*F u) = fun u => G u-Q u :=
    funext fun _ => sub_mul _ _ _
  change _ = 2*∫ u : ℝ, (g u-g (u+b))*F u
  rw [hdiff,integral_sub hG hQ]
  ring

/-- A strictly increasing weight gives a strictly negative limiting
reading. The autocorrelation is positive on a neighborhood of zero. -/
theorem squareLogProfile_test_neg {g : ℝ → ℝ} (hg : Continuous g) (hm : StrictMono g) :
    (∫ u : ℝ, (g u*squareLogProfile u)*Real.exp (u/2)) < 0 := by
  let b := Real.log 4
  let F := fun u : ℝ => (g (u+b)-g u)*(splineAutoCorr u*Real.exp (u/2))
  have hb : 0<b := Real.log_pos (by norm_num)
  have hc : Continuous F := ((hg.comp (continuous_id.add continuous_const)).sub hg).mul
    (continuous_splineAutoCorr.mul (by fun_prop))
  have hk : HasCompactSupport F := autocorr_compact.mul_right.mul_left
  have hdelta (u : ℝ) := sub_pos.mpr (hm (lt_add_of_pos_right u hb))
  have hn (u : ℝ) : 0≤F u := mul_nonneg (hdelta u).le
    (mul_nonneg (splineAutoCorr_nonneg _) (Real.exp_pos _).le)
  have hp : 0<F 0 := mul_pos (hdelta _) (mul_pos splineAutoCorr_zero_pos (Real.exp_pos _))
  have hi := (integral_pos_iff_support_of_nonneg hn (hc.integrable_of_hasCompactSupport hk)).mpr
    (hc.isOpen_support.measure_pos volume ⟨0,hp.ne'⟩)
  rw [squareLogProfile_test_translation hg]
  have he : (fun u : ℝ => (g u-g (u+b))*(splineAutoCorr u*Real.exp (u/2))) = fun u => -F u := by
    funext u; dsimp only [F]; ring
  change 2*(∫ u : ℝ, (g u-g (u+b))*(splineAutoCorr u*Real.exp (u/2))) < 0
  rw [he,integral_neg]
  linarith only [hi]

/-- The first centered logarithmic moment records the full displacement
of the autocorrelation mass by log four. -/
theorem squareLogProfile_first_half_moment :
    (∫ u : ℝ, (u*squareLogProfile u)*Real.exp (u/2)) = -2*Real.log 4*squareAutocorrelationMass := by
  rw [squareLogProfile_test_translation (g := id) continuous_id]
  have h (u : ℝ) : u-(u+Real.log 4) = -Real.log 4 := by ring
  simp only [id_eq,h,integral_const_mul,squareAutocorrelationMass]
  ring

/-- Every continuous test of the logarithmic prime displacement has a
limit against the translated autocorrelation. -/
theorem tendsto_squarePrime_log_test {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun x : ℝ => (∑' p : Nat.Primes,
      Real.log (p:ℕ)*((g (Real.log ((p:ℕ)/x))*squareLogProfile (Real.log ((p:ℕ)/x))) /
        Real.sqrt ((p:ℕ)/x)))/x)
      atTop (𝓝 (∫ u : ℝ, (g u*squareLogProfile u)*Real.exp (u/2))) := by
  have hc : Continuous squareLogProfile := (continuous_const.mul continuous_splineAutoCorr).sub
    (continuous_splineAutoCorr.comp (continuous_id.sub continuous_const))
  have hk : HasCompactSupport squareLogProfile := autocorr_compact.mul_left.sub
    (autocorr_compact.comp_homeomorph (Homeomorph.subRight (Real.log 4)))
  exact tendsto_ordinary_prime_log_test (hg.mul hc) hk.mul_left

/-- The logarithmically tilted ordinary-prime reading converges to a strictly
negative constant on all positive scales tending to infinity. -/
theorem tendsto_squarePrime_first_log_moment :
    Tendsto (fun x : ℝ => (∑' p : Nat.Primes,
      Real.log (p:ℕ)*((Real.log ((p:ℕ)/x)*squareLogProfile (Real.log ((p:ℕ)/x))) /
        Real.sqrt ((p:ℕ)/x)))/x)
      atTop (𝓝 (-2*Real.log 4*squareAutocorrelationMass)) := by
  rw [← squareLogProfile_first_half_moment]
  exact tendsto_squarePrime_log_test (g := id) continuous_id

private theorem square_profile_upper_zero {t : ℝ} (ht : 8+Real.log 4 < t) : squareLogProfile t=0 := by
  have hl := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
  have h₁ : 8 < |t| := by linarith only [ht,hl,le_abs_self t]
  have h₂ : 8 < |t-Real.log 4| := by linarith only [ht,le_abs_self (t-Real.log 4)]
  simp [squareLogProfile,splineAutoCorr_zero_outside h₁,splineAutoCorr_zero_outside h₂]

private theorem profile_below_window (n : ℕ) :
    Real.exp (8+Real.log 4)*(n:ℝ)^2 ≤ ((3*windowEnd ((2*n+1)^2+1):ℕ):ℝ) := by
  have hn : 4*(n:ℝ)^2 ≤ (((2*n+1:ℕ):ℝ))^2 := by
    push_cast
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  have h := (mul_le_mul_of_nonneg_left hn (Real.exp_pos 8).le).trans
    (successorSquareWindowScale_bounds n).2.2
  rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4),Nat.cast_mul,Nat.cast_ofNat]
  linarith only [h,Nat.cast_nonneg (α := ℝ) (windowEnd ((2*n+1)^2+1))]

/-- A logarithmic test of the fixed profile uses exactly the finite ordinary
prime window, as every later prime lies beyond both spline overlaps. -/
theorem diagonal_prime_test_window {n : ℕ} (hn : 0<n) (g : ℝ → ℝ) :
    (∑' p : Nat.Primes, Real.log (p:ℕ)*
      ((g (Real.log ((p:ℕ)/((n:ℝ)^2)))*squareLogProfile (Real.log ((p:ℕ)/((n:ℝ)^2))))/
        Real.sqrt ((p:ℕ)/((n:ℝ)^2)))) =
    ∑ k ∈ ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1)), Real.log k*
      ((g (Real.log ((k:ℝ)/((n:ℝ)^2)))*squareLogProfile (Real.log ((k:ℝ)/((n:ℝ)^2))))/
        Real.sqrt ((k:ℝ)/((n:ℝ)^2))) := by
  classical
  let X := (n:ℝ)^2
  let L := 3*windowEnd ((2*n+1)^2+1)
  let f := fun k : ℕ => Real.log k*((g (Real.log (k/X))*squareLogProfile (Real.log (k/X)))/Real.sqrt (k/X))
  let F := fun k : ℕ => if k.Prime then f k else 0
  have hsub : (∑' p : Nat.Primes, F p.val)=∑' k : ℕ, F k := by
    apply tsum_subtype_eq_of_support_subset (s := {k : ℕ | k.Prime})
    intro k hk
    by_contra h
    exact hk (if_neg h)
  have hX : 0<X := sq_pos_of_pos (Nat.cast_pos.mpr hn)
  calc _ = ∑' p : Nat.Primes, F p.val := tsum_congr fun p => (if_pos p.property).symm
    _ = ∑' k : ℕ, F k := hsub
    _ = ∑ k ∈ ordinaryPrimeLags L, F k := tsum_eq_sum fun k hk => by
      by_cases hp : k.Prime
      · have hL : L<k := lt_of_not_ge fun h => hk (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le,h⟩,hp⟩)
        have hcut := (profile_below_window n).trans_lt (by exact_mod_cast hL : (L:ℝ)<k)
        have hlog := (Real.lt_log_iff_exp_lt (div_pos (Nat.cast_pos.mpr hp.pos) hX)).mpr
          ((lt_div_iff₀ hX).mpr hcut)
        simp [F,f,hp,square_profile_upper_zero hlog]
      · exact if_neg hp
    _ = _ := Finset.sum_congr rfl fun _ hk => if_pos (Finset.mem_filter.mp hk).2

/-- The finite prime window suffices for every continuous logarithmic test. -/
theorem tendsto_diagonal_finite_prime_test {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun n : ℕ => (∑ k ∈ ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1)), Real.log k*
      ((g (Real.log ((k:ℝ)/(n:ℝ)^2))*squareLogProfile (Real.log ((k:ℝ)/(n:ℝ)^2)))/Real.sqrt ((k:ℝ)/(n:ℝ)^2)))/(n:ℝ)^2)
      atTop (𝓝 (∫ u : ℝ, (g u*squareLogProfile u)*Real.exp (u/2))) := by
  have ht := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop
  refine ((tendsto_squarePrime_log_test hg).comp ht).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact congrArg (·/(n:ℝ)^2) (diagonal_prime_test_window hn g)

/-- The first centered logarithmic moment of the valuations predicted by
the dyadic profile has a strictly negative cubic leading coefficient. -/
theorem tendsto_diagonal_finite_prime_log_moment :
    Tendsto (fun n : ℕ => (∑ k ∈ ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1)), Real.log k*
      ((Real.log ((k:ℝ)/(n:ℝ)^2)*squareLogProfile (Real.log ((k:ℝ)/(n:ℝ)^2)))/Real.sqrt ((k:ℝ)/(n:ℝ)^2)))/(n:ℝ)^2)
      atTop (𝓝 (-2*Real.log 4*squareAutocorrelationMass)) := by
  rw [← squareLogProfile_first_half_moment]
  exact tendsto_diagonal_finite_prime_test (g := id) continuous_id

#print axioms tendsto_diagonal_finite_prime_log_moment
#print axioms squareAutocorrelationMass_pos
#print axioms squareLogProfile_test_neg
#print axioms squareLogProfile_first_half_moment
#print axioms tendsto_squarePrime_first_log_moment

end GaloisForLFunctions.CountingHolography.Sections
