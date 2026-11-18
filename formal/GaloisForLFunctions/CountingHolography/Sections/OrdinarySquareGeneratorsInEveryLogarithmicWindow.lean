import GaloisForLFunctions.CountingHolography.Sections.TheThetaMeanOfTheSquareTrace
import GaloisForLFunctions.CountingHolography.Sections.TheSignedDegreeAtTheNearestUpperSquare
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PrimeLogarithmicWindows
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape

/-!
# Ordinary square generators in every late logarithmic window

The positive theta source annihilates both long lags. If they stayed
below minus one across the window, its exponentially small tail could
not cancel the fixed local deficit. At the resulting integer square
the same rational power bound covers every positive multiplicity.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology MeasureTheory ArithmeticScatteringHolography
open SurfaceOfSpecZ.ScaleLocality _root_.RHTower

private abbrev phi := thetaCuspFullSource

/-- Some point of each late logarithmic window has long trace at least minus one. -/
private theorem long_trace_in_every_window : ∀ᶠ T : ℝ in atTop, ∃ u : ℝ,
    |u-T| ≤ 8*Real.log (T+2) ∧ -1 ≤ squareLongTrace u := by
  obtain ⟨A,hA,habs⟩ := squareLongTrace_bound
  obtain ⟨C,hC,hθ⟩ := exists_theta_logarithmic_moment_bound
  let F := fun u => -squareLongTrace u-1
  have hF (u : ℝ) : |F u| ≤ (A+1)*Real.exp (1/2*|u|) := by
    have hh := abs_sub_le (-squareLongTrace u) 0 1
    simp only [sub_zero,zero_sub,abs_neg,abs_one] at hh
    dsimp only [F]
    linarith only [hh,habs u,Real.one_le_exp (show 0 ≤ 1/2*|u| by positivity)]
  have hi : Integrable phi := by
    simpa only [zero_mul,Real.exp_zero,one_mul] using HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource 0
  have hlim := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul ((A+1)*C)
  rw [mul_zero] at hlim
  filter_upwards [eventually_ge_atTop 6,eventually_ge_atTop (Real.exp 2),
    hlim.eventually_lt_const integral_thetaCuspFullSource_pos] with T hT hlate hsmall
  by_contra! hbad
  have hlog : (2:ℝ) ≤ Real.log (T+2) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) (hlate.trans (show T ≤ T+2 by linarith))
  have he (x : ℝ) : phi x*F (T+x) = -(phi x*squareLongTrace (T+x))-phi x := by
    dsimp only [F]; ring
  have hneg : Integrable (fun x => -(phi x*squareLongTrace (T+x))) := by
    simpa only [neg_one_mul] using (thetaMean_squareLongTrace T).1.const_mul (-1:ℝ)
  have hFi : Integrable fun x => phi x*F (T+x) := by
    simp_rw [he]
    exact hneg.sub hi
  have hlocal (x : ℝ) (hx : |x| ≤ 8*Real.log (T+2)) : -(0:ℝ) ≤ F (T+x) := by
    have h := hbad (T+x) (by simpa only [add_sub_cancel_left] using hx)
    dsimp only [F]; linarith only [h]
  have ht := positive_kernel_logarithmic_floor (A := A+1) (C := C) (b := 1/2) (D := 1/2)
    (K := 0) (B := 0) (t := T) (by positivity) hC.le (by norm_num) (by linarith only [hT])
    (by norm_num) le_rfl hT (by linarith only [hlog]) (by rw [abs_of_nonneg (by linarith only [hT] : 0 ≤ T),add_zero])
    (fun x => (thetaCuspFullSource_pos x).le) hi (HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource _)
    hFi hF (hθ _ (by linarith only [hT])) hlocal
  simp_rw [he] at ht
  rw [integral_sub hneg hi,integral_neg,(thetaMean_squareLongTrace T).2] at ht
  simp only [neg_zero,zero_mul,mul_zero,zero_sub] at ht
  linarith only [ht,hsmall]

/-- The same base buys every positive multiplicity whenever the signed
degree has a fixed lower bound. Small multiplicities spend the ordinary floors. -/
theorem all_ordinary_generators_of_degree_floor (D : ℝ) :
    ∃ B : ℕ, 0 < B ∧ ∀ᶠ n : ℕ in atTop, -D ≤ integerProbe _ (successorSquareTriple n) →
      ∀ {m : ℕ}, 0 < m → ordinaryPrimeGenerator (m • successorSquareTriple n) ≤ (B:ℚ)^(m^2) := by
  obtain ⟨A,_,hA⟩ := successorSquare_contact_degree
  obtain ⟨C,hC,hmesh⟩ := successorSquare_floor_corrected_mesh_error
  obtain ⟨c,hc,hfloor⟩ := all_multiplicities_through_diagonal_ordinary_floor_loss (K := 1) le_rfl
  let B := ⌈Real.exp (A+D+C)⌉₊
  have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hlog : A+D+C ≤ Real.log B := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil _)
  refine ⟨B,hB,?_⟩
  filter_upwards [hfloor,eventually_ge_atTop 1,eventually_ge_atTop ⌈C/c⌉₊] with n hf hn hnC hQ m hm
  have hP : ordinaryPrimeContact (successorSquareTriple n) ≤ A+D := by
    linarith only [(abs_le.mp (hA hn)).2,hQ]
  let a := m • successorSquareTriple n
  have herr := (abs_le.mp (hmesh hn m)).2
  have hV : C*n ≤ ordinaryFloorLoss a+C*(m:ℝ)^2 := by
    by_cases hmn : m ≤ n
    · have hfit : (m:ℝ) ≤ 1*squareUpperRoot n := by
        unfold squareUpperRoot
        have hh : (m:ℝ) ≤ n := by exact_mod_cast hmn
        linarith only [hh,Nat.cast_nonneg (α := ℝ) n]
      have hCn : C ≤ (n:ℝ)*c := (div_le_iff₀ hc).mp ((Nat.le_ceil _).trans (by exact_mod_cast hnC))
      linarith only [hf hm hfit,mul_le_mul_of_nonneg_right hCn (Nat.cast_nonneg (α := ℝ) n),
        mul_nonneg hC (sq_nonneg (m:ℝ))]
    · have hnm : (n:ℝ) ≤ m := by exact_mod_cast (le_of_lt (lt_of_not_ge hmn))
      have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
      have hh : (n:ℝ) ≤ (m:ℝ)^2 := hnm.trans (by nlinarith only [mul_le_mul_of_nonneg_right hm1 (Nat.cast_nonneg (α := ℝ) m)])
      linarith only [(ordinaryFloorLoss_bounds a).1,mul_le_mul_of_nonneg_left hh hC]
  have hb := generator_le_power_iff a hB 1 m
  simp only [one_mul,Nat.cast_one,one_pow,mul_one] at hb
  apply hb.mpr
  change Real.log (ordinaryPrimeGenerator a:ℝ) + ordinaryFloorLoss a -
    (m:ℝ)^2*ordinaryPrimeContact (successorSquareTriple n) ≤ C*n at herr
  linarith only [herr,hV,mul_le_mul_of_nonneg_left hP (sq_nonneg (m:ℝ)),mul_le_mul_of_nonneg_right hlog (sq_nonneg (m:ℝ))]

/-- Every sufficiently late logarithmic window contains a square conductor
whose ordinary generator obeys one fixed rational power bound at every
multiplicity, including its original diagonal multiplicity. -/
theorem ordinary_square_generators_in_every_logarithmic_window :
    ∃ B : ℕ, 0 < B ∧ ∀ᶠ T : ℝ in atTop, ∃ n : ℕ, 0 < n ∧
      |2*Real.log n-T| ≤ 10*Real.log (T+2) ∧
      ∀ {m : ℕ}, 0 < m → ordinaryPrimeGenerator (m • successorSquareTriple n) ≤ (B:ℚ)^(m^2) := by
  let b := 6*realSplineTrace 0-4*realSplineTrace (Real.log 4)
  obtain ⟨B,hB,hpaid⟩ := all_ordinary_generators_of_degree_floor (2-b)
  obtain ⟨U,hU⟩ := eventually_atTop.mp ((tendsto_upperSquareIndex.eventually hpaid).and
    (upperSquareIndex_signed_degree.eventually_const_lt (show b-1 < b by linarith)))
  refine ⟨B,hB,?_⟩
  filter_upwards [long_trace_in_every_window,primeLogarithmicRadius_shape,eventually_ge_atTop (2*|U|),
    eventually_ge_atTop (Real.exp 1)] with T ⟨u,hu,htrace⟩ hs hT heT
  have hr : 32*Real.log (T+2) ≤ T := hs.2
  have hlog : 1 ≤ Real.log (T+2) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (heT.trans (show T ≤ T+2 by linarith))
  have hu₀ : 0 ≤ u := by linarith only [(abs_le.mp hu).1,hr,hlog]
  have huU : U ≤ u := by linarith only [(abs_le.mp hu).1,hr,hT,le_abs_self U,hlog]
  obtain ⟨hp,hq⟩ := hU u huU
  let n := upperSquareIndex u
  have hQ : -(2-b) ≤ integerProbe _ (successorSquareTriple n) := by
    change b-1 < integerProbe _ (successorSquareTriple n)-squareLongTrace u at hq
    linarith only [hq,htrace]
  refine ⟨n,upperSquareIndex_pos u,?_,hp hQ⟩
  obtain ⟨hl,hu'⟩ := upperSquareIndex_log_near hu₀
  rw [abs_le]
  obtain ⟨h₁,h₂'⟩ := abs_le.mp hu
  constructor <;> linarith only [hl,hu',h₁,h₂',hlog]

#print axioms ordinary_square_generators_in_every_logarithmic_window

end GaloisForLFunctions.CountingHolography.Sections
